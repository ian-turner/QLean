import QLean.Program.Type
import QLean.Circuit.Embed

/-!
# Program denotation: rewriting lemmas

Equational facts about `Program.denote` used when relating a program to a target circuit:

* `denote_foldr_seq` — `denote` pushes through a right-fold of sequenced gates (a homomorphism).
* `denote_relabel`   — re-addressing a program through `f` denotes to the *embedding* of its
  denotation (`denote (relabel f p) ≈ embed f (denote p)`), via the circuit-level `embed` algebra.

`QCircuit.embed_congr` (embedding respects `≈`) is added here as well — it is the congruence the
relabel/`par`-bridge reasoning needs.
-/

open scoped QLean.Notation
open scoped Matrix

namespace QLean

namespace QCircuit

variable {n k : ℕ}

/-- Embedding respects circuit equivalence: equivalent sub-circuits embed to equivalent circuits.
    Tagged `@[gcongr]` so `grw`/`gcongr` can rewrite under an `embed`. -/
@[gcongr]
theorem embed_congr (qs : Fin k ↪ Fin n) {c₁ c₂ : QCircuit k} (h : c₁ ≈ c₂) :
    QCircuit.embed qs c₁ ≈ QCircuit.embed qs c₂ := by
  simp only [Equiv, eval_embed]
  exact congrArg (QLean.embed qs) h

end QCircuit

namespace Program

variable {n m : ℕ}

/-- `denote` is a homomorphism through a right-fold of sequenced gates: it commutes with the fold,
    turning each program factor into its denotation. (A genuine equality — each step is `denote_seq`,
    which is `rfl`.) -/
theorem denote_foldr_seq {α : Type*} (l : List α) (P : α → Program n) (init : Program n) :
    (l.foldr (fun a acc => P a * acc) init).denote
      = l.foldr (fun a acc => (P a).denote * acc) init.denote := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, Program.denote_seq, ih]

/-- Re-addressing a program through `f` denotes to the embedding of its denotation. Proved by
    induction on the program using the circuit-level `embed` algebra: `embed_id` (identity),
    `embed_comp` (a prim's `qs` composes with `f`), and `embed_seq` (distribution over `*`). -/
theorem denote_relabel (f : Fin n ↪ Fin m) (p : Program n) :
    (p.relabel f).denote ≈ QCircuit.embed f p.denote := by
  induction p with
  | id => exact (QCircuit.embed_id f).symm
  | prim g qs => exact (QCircuit.embed_comp f qs (.gate g.matrix)).symm
  | seq p q ihp ihq =>
    show (relabel f p).denote * (relabel f q).denote ≈ QCircuit.embed f (p.denote * q.denote)
    grw [ihp, ihq]
    exact (QCircuit.embed_seq f p.denote q.denote).symm

end Program

end QLean
