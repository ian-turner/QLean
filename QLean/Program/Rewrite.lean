import QLean.Program.Type
import QLean.Circuit.Embed

/-!
# Program denotation: rewriting lemmas and program equivalence

Notation (scoped in `QLean.Notation`, alongside `⟦p⟧` from `Program/Type.lean`): `p ⇓ c`
states that the program `p` denotes a circuit equivalent to `c`. It is pure sugar for
`⟦p⟧ ≈ c` — no new relation is introduced, so all circuit-`≈` machinery applies as-is.

Equational facts about `Program.denote` used when relating a program to a target circuit:

* `denote_foldr_seq` — `denote` pushes through a right-fold of sequenced gates (a homomorphism).
* `denote_relabel`   — re-addressing a program through `f` denotes to the *embedding* of its
  denotation (`p.relabel f ⇓ QCircuit.embed f ⟦p⟧`), via the circuit-level `embed` algebra.

`Program.Equiv` (`p ≈ q` iff the denotations are equivalent circuits) lives here too, with the
refl/symm/trans and congruence kit (`Equiv.seq_congr`, `Equiv.relabel_congr`, `denote_congr`)
that makes program-level `calc`/`grw` rewriting possible.

`QCircuit.embed_congr` (embedding respects `≈`) is added here as well — it is the congruence the
relabel/`par`-bridge reasoning needs.
-/

namespace QLean.Notation

/-- `p ⇓ c` : the program `p` denotes a circuit equivalent to `c`. Pure notation for
    `⟦p⟧ ≈ c` — the proposition's head is still the circuit-level `≈`, so `calc`, `grw`,
    `.symm`/`.trans`, and every existing `≈`-lemma apply directly. Opt in with
    `open scoped QLean.Notation`. -/
scoped notation:50 p:51 " ⇓ " c:51 => HasEquiv.Equiv (QLean.Program.denote p) c

end QLean.Notation

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
    ⟦l.foldr (fun a acc => P a * acc) init⟧
      = l.foldr (fun a acc => ⟦P a⟧ * acc) ⟦init⟧ := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, Program.denote_seq, ih]

/-- Re-addressing a program through `f` denotes to the embedding of its denotation. Proved by
    induction on the program using the circuit-level `embed` algebra: `embed_id` (identity),
    `embed_comp` (a prim's `qs` composes with `f`), and `embed_seq` (distribution over `*`). -/
theorem denote_relabel (f : Fin n ↪ Fin m) (p : Program n) :
    p.relabel f ⇓ QCircuit.embed f ⟦p⟧ := by
  induction p with
  | id => exact (QCircuit.embed_id f).symm
  | prim g qs => exact (QCircuit.embed_comp f qs (.gate g.matrix)).symm
  | seq p q ihp ihq =>
    show ⟦relabel f p⟧ * ⟦relabel f q⟧ ≈ QCircuit.embed f (⟦p⟧ * ⟦q⟧)
    grw [ihp, ihq]
    exact (QCircuit.embed_seq f ⟦p⟧ ⟦q⟧).symm

-- ── Program equivalence ───────────────────────────────────────────────────────

/-- Two programs are equivalent if they denote equivalent circuits (i.e. they evaluate to
    the same unitary). -/
def Equiv (p q : Program n) : Prop := ⟦p⟧ ≈ ⟦q⟧

-- `p ≈ q` is notation for `Program.Equiv p q`.
@[reducible] instance : HasEquiv (Program n) := ⟨Equiv⟩

@[refl]  theorem Equiv.refl  (p : Program n) : p ≈ p := rfl
@[symm]  theorem Equiv.symm  {p q : Program n} : p ≈ q → q ≈ p := QCircuit.Equiv.symm
@[trans] theorem Equiv.trans {p q r : Program n} : p ≈ q → q ≈ r → p ≈ r :=
  QCircuit.Equiv.trans

instance : Trans (@Equiv n) (@Equiv n) (@Equiv n) := ⟨Equiv.trans⟩

/-- Denotation respects program equivalence (definitionally — `p ≈ q` *is* `⟦p⟧ ≈ ⟦q⟧`).
    Tagged `@[gcongr]` so `grw` can rewrite under `⟦·⟧` with a program-level equivalence. -/
@[gcongr] theorem denote_congr {p q : Program n} (h : p ≈ q) : ⟦p⟧ ≈ ⟦q⟧ := h

/-- Equivalent components yield equivalent sequenced programs. -/
@[gcongr]
theorem Equiv.seq_congr {p p' q q' : Program n} (h₁ : p ≈ p') (h₂ : q ≈ q') :
    p * q ≈ p' * q' :=
  QCircuit.Equiv.seq_congr h₁ h₂

/-- Re-addressing respects program equivalence. -/
@[gcongr]
theorem Equiv.relabel_congr (f : Fin n ↪ Fin m) {p q : Program n} (h : p ≈ q) :
    p.relabel f ≈ q.relabel f := by
  show ⟦p.relabel f⟧ ≈ ⟦q.relabel f⟧
  calc ⟦p.relabel f⟧ ≈ QCircuit.embed f ⟦p⟧ := denote_relabel f p
    _ ≈ QCircuit.embed f ⟦q⟧ := QCircuit.embed_congr f h
    _ ≈ ⟦q.relabel f⟧ := (denote_relabel f q).symm

/-- `1` is a left identity for sequencing, up to `≈`. -/
theorem seq_id_left (p : Program n) : 1 * p ≈ p := QCircuit.seq_id_left ⟦p⟧

/-- `1` is a right identity for sequencing, up to `≈`. -/
theorem seq_id_right (p : Program n) : p * 1 ≈ p := QCircuit.seq_id_right ⟦p⟧

/-- Sequencing is associative up to `≈`. -/
theorem seq_assoc (p q r : Program n) : (p * q) * r ≈ p * (q * r) :=
  QCircuit.seq_assoc ⟦p⟧ ⟦q⟧ ⟦r⟧

end Program

end QLean
