import QLean.Gate.Standard
import QLean.State.Rewrite

open scoped QLean.Notation

namespace QLean

noncomputable section

-- ── Single-qubit gate actions on symbolic states ──────────────────────────────

-- Both `HasEquiv (QState n)` and `HasEquiv (Circuit n)` are in scope (from
-- Circuit.Rewrite), so Lean cannot propagate the expected type through `≈` to
-- determine `n` in ket literals.  Annotating the ket argument directly resolves this.
--
-- `simp only` reduces the goal to the QVector level; `exact` closes it via
-- the kernel's full definitional equality (which handles Fin (2^1) = Fin 2).

theorem XGate_bit0 : XGate * (|0⟩ : QState 1) ≈ (|1⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, Circuit.eval_gate]
  exact X_ket_zero

theorem XGate_bit1 : XGate * (|1⟩ : QState 1) ≈ (|0⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, Circuit.eval_gate]
  exact X_ket_one

theorem YGate_bit0 : YGate * (|0⟩ : QState 1) ≈ Complex.I • (|1⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             Circuit.eval_gate]
  exact Y_ket_zero

theorem YGate_bit1 : YGate * (|1⟩ : QState 1) ≈ (-Complex.I) • (|0⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             Circuit.eval_gate]
  exact Y_ket_one

theorem ZGate_bit0 : ZGate * (|0⟩ : QState 1) ≈ (|0⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, Circuit.eval_gate]
  exact Z_ket_zero

theorem ZGate_bit1 : ZGate * (|1⟩ : QState 1) ≈ (-1 : ℂ) • (|1⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             Circuit.eval_gate]
  exact Z_ket_one

theorem SGate_bit0 : SGate * (|0⟩ : QState 1) ≈ (|0⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, Circuit.eval_gate]
  exact S_ket_zero

theorem SGate_bit1 : SGate * (|1⟩ : QState 1) ≈ Complex.I • (|1⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             Circuit.eval_gate]
  exact S_ket_one

-- `((Real.sqrt 2)⁻¹ : ℂ)` elaborates as `(↑(Real.sqrt 2))⁻¹` (ℂ-inverse after coercion),
-- while `H_ket_zero` has `(Real.sqrt 2)⁻¹ : ℝ` (ℝ-smul on QVector).
-- `← Complex.ofReal_inv` rewrites `(↑r)⁻¹ → ↑(r⁻¹)`, then `algebraMap_smul`
-- converts the ℂ-smul to ℝ-smul so `exact H_ket_zero` closes the goal.
theorem HGate_bit0 :
    HGate * (|0⟩ : QState 1) ≈ ((Real.sqrt 2)⁻¹ : ℂ) • ((|0⟩ : QState 1) + |1⟩) := by
  simp only [QState.Equiv, QState.eval_apply, Circuit.eval_gate, QState.eval_smul,
             QState.eval_add, QState.eval_basis, ← Complex.ofReal_inv]
  exact H_ket_zero

theorem HGate_bit1 :
    HGate * (|1⟩ : QState 1) ≈ ((Real.sqrt 2)⁻¹ : ℂ) • ((|0⟩ : QState 1) + (-1 : ℂ) • |1⟩) := by
  simp only [QState.Equiv, QState.eval_apply, Circuit.eval_gate, QState.eval_smul,
             QState.eval_add, QState.eval_basis, ← Complex.ofReal_inv]
  exact H_ket_one

-- ── Two-qubit gate actions ─────────────────────────────────────────────────────

/-- CNOT maps `|a⟩ ⊗ₛ |b⟩` to `|a⟩ ⊗ₛ |a+b⟩` (XOR on the target qubit).
    Variables have type `Fin (2^1)` so they directly match the ket index type. -/
theorem CNOTGate_basis_tensor (a b : Fin (2^1)) :
    CNOTGate * ((|a⟩ : QState 1) ⊗ₛ (|b⟩ : QState 1)) ≈
    (|a⟩ : QState 1) ⊗ₛ (|a + b⟩ : QState 1) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_tensor, QState.eval_basis,
             Circuit.eval_gate, ket_tensorState]
  exact CNOT_ket_pair a b

end

end QLean
