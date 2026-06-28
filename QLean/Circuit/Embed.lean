import QLean.Circuit.Rewrite
import QLean.Basic.EmbedState

/-!
# Circuit-level algebra of the `embed` constructor

`Circuit/Type.lean` makes `embed qs c` a first-class circuit former and `Circuit/Semantics.lean`
interprets it by the matrix `embed` of `Basic/Embed.lean` (`eval (embed qs c) = embed qs (eval c)`).
This file lifts the *matrix* algebra of `embed` to the *circuit* layer as `≈`-lemmas, so structural
reasoning and circuit-to-circuit transformations can push embeddings around without dropping to
matrices:

* `embed_gate`        — bridge: embedding a single gate is the gate of the embedded matrix.
* `embed_id`          — embedding the identity is the identity.
* `embed_seq`         — embedding distributes over sequential composition.
* `embed_comp`        — nested embeddings compose their addressing maps (`qs2.trans qs`).
* `embed_par_split`   — a parallel sub-circuit splits into its low/high halves embedded separately.
* `embed_comm_disjoint` — embedded sub-circuits on disjoint qubit sets commute.

The headline action lemmas (`embed_diag_action`, `embed_single_action`) describe how an embedded
gate acts on a computational basis ket; they are the entry points the per-layer correctness proofs
(e.g. the QFT) actually use, lifting the `Basic/EmbedState.lean` matrix facts to the `QState` layer.
-/

open scoped QLean.Notation
open scoped Matrix

namespace QLean

namespace QCircuit

noncomputable section

variable {n k m : ℕ}

-- ── Circuit-level algebra (every step reduces to the matrix algebra of `Basic/Embed`) ──

/-- Embedding a single gate is the gate of the embedded matrix — the bridge between the
    first-class `embed` constructor and the matrix `embed` of `Basic/Embed.lean`. -/
theorem embed_gate (qs : Fin k ↪ Fin n) (U : QMatrix k) :
    QCircuit.embed qs (gate U) ≈ gate (QLean.embed qs U) := rfl

/-- Embedding the identity circuit is the identity. -/
theorem embed_id (qs : Fin k ↪ Fin n) :
    QCircuit.embed qs (1 : QCircuit k) ≈ (1 : QCircuit n) := by
  simp only [Equiv, eval_embed, eval_id, embed_one]

/-- Embedding distributes over sequential composition. -/
theorem embed_seq (qs : Fin k ↪ Fin n) (c₁ c₂ : QCircuit k) :
    QCircuit.embed qs (c₁ * c₂) ≈ QCircuit.embed qs c₁ * QCircuit.embed qs c₂ := by
  simp only [Equiv, eval_embed, eval_seq, embed_mul]

/-- Nested embeddings compose their addressing maps: embedding through `qs2` then `qs` is
    embedding through the composite `qs2.trans qs`. -/
theorem embed_comp (qs : Fin k ↪ Fin n) (qs2 : Fin m ↪ Fin k) (c : QCircuit m) :
    QCircuit.embed qs (QCircuit.embed qs2 c) ≈ QCircuit.embed (qs2.trans qs) c := by
  simp only [Equiv, eval_embed, embed_embed]

/-- A parallel sub-circuit `c₁ ⊗ c₂` embedded at `qs` factors into `c₁` embedded at the low half
    of `qs` and `c₂` embedded at the high half — the structural form of `embed_kron_factor`. -/
theorem embed_par_split {j k : ℕ} (qs : Fin (j + k) ↪ Fin n)
    (c₁ : QCircuit j) (c₂ : QCircuit k) :
    QCircuit.embed qs (c₁ ⊗ c₂)
      ≈ QCircuit.embed ((lowEmb j k).trans qs) c₁ * QCircuit.embed ((highEmb j k).trans qs) c₂ := by
  simp only [Equiv, eval_embed, eval_seq, eval_par, embed_kron_factor]

/-- A bare parallel composition is two embeddings on the disjoint low/high coordinate blocks — the
    bridge that lets a structural pass rewrite a `par` into the uniform `embed` view (`embed_par_split`
    is the already-embedded form). -/
theorem par_as_embed {j k : ℕ} (c₁ : QCircuit j) (c₂ : QCircuit k) :
    (c₁ ⊗ c₂ : QCircuit (j + k))
      ≈ QCircuit.embed (lowEmb j k) c₁ * QCircuit.embed (highEmb j k) c₂ := by
  simp only [Equiv, eval_seq, eval_embed, eval_par, kron_eq_embed]

/-- Sub-circuits embedded at disjoint qubit sets commute. -/
theorem embed_comm_disjoint {j k : ℕ} (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n)
    (hdisj : ∀ (a : Fin j) (b : Fin k), qs₁ a ≠ qs₂ b) (c₁ : QCircuit j) (c₂ : QCircuit k) :
    QCircuit.embed qs₁ c₁ * QCircuit.embed qs₂ c₂
      ≈ QCircuit.embed qs₂ c₂ * QCircuit.embed qs₁ c₁ := by
  simp only [Equiv, eval_seq, eval_embed]
  exact QLean.embed_comm_disjoint qs₁ qs₂ hdisj (eval c₁) (eval c₂)

-- ── Action of an embedded gate on a basis ket (entry points for correctness proofs) ──

/-- A diagonal gate embedded at `qs` scales a basis ket by its eigenvalue on the selected bits —
    no superposition, whatever qubits `qs` addresses. The entry point for embedded phase /
    controlled-rotation layers. -/
theorem embed_diag_action (qs : Fin k ↪ Fin n) {U : QMatrix k} (hU : Matrix.IsDiag U)
    (i : Fin (2 ^ n)) :
    QCircuit.embed qs (gate U) * (❘i⟩ : QState n)
      ≈ U (selectIdx qs i) (selectIdx qs i) • ❘i⟩ := by
  simp only [QState.Equiv, QState.eval_apply, eval_embed, eval_gate, QState.eval_smul,
    QState.eval_basis]
  exact embed_diag_mul_ket hU i

/-- A 1-qubit gate embedded at the single qubit `qs 0` splits a basis ket into the two indices
    that clear / set that qubit, weighted by the gate's column at the current bit. The entry point
    for an embedded single-qubit gate (e.g. a positionally placed Hadamard). -/
theorem embed_single_action (qs : Fin 1 ↪ Fin n) (U : QMatrix 1) (i : Fin (2 ^ n)) :
    QCircuit.embed qs (gate U) * (❘i⟩ : QState n)
      ≈ U 0 (selectIdx qs i) • ❘mergeBits qs i 0⟩
        + U 1 (selectIdx qs i) • ❘mergeBits qs i 1⟩ := by
  simp only [QState.Equiv, QState.eval_apply, eval_embed, eval_gate, QState.eval_add,
    QState.eval_smul, QState.eval_basis]
  exact embed_single_mul_ket qs U i

end  -- noncomputable

end QCircuit

end QLean
