import QLean
import Examples.CliffordConjugation

/-!
# Controlled-gate conjugation and the controlled-S decomposition

Two results about `controlled U` (Fenner Exercises 11.4(3) and 13.2(1)):

* **Target conjugation, parametric in `U` and `A`**:
  `C-(U A U†) = (1 ⊗ U) · C-A · (1 ⊗ U†)` for any unitary `U` and any `A` — conjugating
  the target leg of a controlled gate conjugates the gate it controls. The CNOT ↔ CZ
  bridge of `Examples/CNOTCZ.lean` is the `U = H, A = Z/X` instance.

* **`C-S = (T ⊗ T) · CNOT · (1 ⊗ T†) · CNOT`**: the controlled-S from two CNOTs and
  three T-family gates, the inner step of the standard Toffoli decomposition.

Both proofs are control-splits: the `❘0⟩` branch is unitarity cancellation on the target,
the `❘1⟩` branch is the underlying 1-qubit identity — no superpositions anywhere.
-/

open scoped QLean.Notation
open scoped Matrix

namespace QLean.Examples

open QLean

noncomputable section

local notation "id1" => (1 : QCircuit 1)

-- ── Target conjugation (Fenner Ex 11.4(3)) ────────────────────────────────────

/-- `C-(U A U†) ≈ (1 ⊗ U) · C-A · (1 ⊗ U†)` for unitary `U`. -/
theorem controlled_conj (U A : QMatrix 1) (hU : IsUnitary U) :
    ControlledGate (U * A * Uᴴ)
      ≈ (id1 ⊗ QCircuit.gate U) * ControlledGate A * (id1 ⊗ QCircuit.gate Uᴴ) := by
  -- unitarity, in action form: `U (U† s) ≈ s`
  have h1 : QCircuit.gate U * QCircuit.gate Uᴴ ≈ (1 : QCircuit 1) := by
    simp only [QCircuit.Equiv, QCircuit.eval_seq, QCircuit.eval_gate, QCircuit.eval_id]
    exact hU
  have cancel : ∀ s : QState 1, QCircuit.gate U * (QCircuit.gate Uᴴ * s) ≈ s := fun s =>
    ((QCircuit.seq_action _ _ _).symm).trans ((h1.apply_state s).trans (QCircuit.id_action s))
  -- unfold the conjugated gate into a three-step action
  have expand : ∀ s : QState 1, QCircuit.gate (U * A * Uᴴ) * s
      ≈ QCircuit.gate U * (QCircuit.gate A * (QCircuit.gate Uᴴ * s)) := fun s =>
    ((QCircuit.gate_seq (U * A) Uᴴ).apply_state s).trans
      ((QCircuit.seq_action _ _ _).trans
        (((QCircuit.gate_seq U A).apply_state _).trans (QCircuit.seq_action _ _ _)))
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, ControlledGate_zero A, QCircuit.par_action_tensor,
         QCircuit.id_action, cancel, ControlledGate_zero (U * A * Uᴴ)]
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, ControlledGate_one A, QCircuit.par_action_tensor,
         QCircuit.id_action, ControlledGate_one (U * A * Uᴴ), expand]

-- ── Controlled-S from CNOTs and T gates (Fenner Ex 13.2(1)) ───────────────────

-- The two phase facts the decomposition bottoms out at.
private lemma t_phase_cancel' :
    Complex.exp (-(Complex.I * Real.pi / 4)) * Complex.exp (Complex.I * Real.pi / 4) = 1 := by
  rw [← Complex.exp_add]
  norm_num

private lemma t_phase_double :
    Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)
      = Complex.I := by
  rw [← Complex.exp_add,
      show Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
         = (Real.pi / 2 : ℝ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
  push_cast; simp

/-- `C-S ≈ (T ⊗ T) · CNOT · (1 ⊗ T†) · CNOT`. -/
theorem controlled_s_decomp :
    ControlledGate S ≈ (TGate ⊗ TGate) * CNOTGate * (id1 ⊗ TdgGate) * CNOTGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
  · -- |00⟩: everything fixes the state
    grw [ControlledGate_zero, QCircuit.seq_action, QCircuit.seq_action,
         QCircuit.seq_action, CNOTGate_basis_tensor 0 0,
         show (0 : Fin (2^1)) + 0 = 0 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, TdgGate_bit0,
         CNOTGate_basis_tensor 0 0, show (0 : Fin (2^1)) + 0 = 0 by decide,
         QCircuit.par_action_tensor, TGate_bit0]
  · -- |01⟩ (control 0, target 1): T and T† phases on the target cancel
    grw [ControlledGate_zero, QCircuit.seq_action, QCircuit.seq_action,
         QCircuit.seq_action, CNOTGate_basis_tensor 0 1,
         show (0 : Fin (2^1)) + 1 = 1 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, TdgGate_bit1,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 0 1,
         show (0 : Fin (2^1)) + 1 = 1 by decide,
         QCircuit.apply_smul, QCircuit.par_action_tensor, TGate_bit0, TGate_bit1,
         QState.tensor_smul_right, QState.smul_smul,
         QState.smul_scalar_congr t_phase_cancel', QState.one_smul]
  · -- |10⟩ (control 1, target 0): the T on the control cancels against T† via the XORs
    grw [ControlledGate_one, SGate_bit0, QCircuit.seq_action, QCircuit.seq_action,
         QCircuit.seq_action, CNOTGate_basis_tensor 1 0,
         show (1 : Fin (2^1)) + 0 = 1 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, TdgGate_bit1,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 1 1,
         show (1 : Fin (2^1)) + 1 = 0 by decide,
         QCircuit.apply_smul, QCircuit.par_action_tensor, TGate_bit1, TGate_bit0,
         QState.smul_tensor_left, QState.smul_smul,
         QState.smul_scalar_congr t_phase_cancel', QState.one_smul]
  · -- |11⟩: T·T on the diagonal gives the S phase i
    grw [ControlledGate_one, SGate_bit1, QState.tensor_smul_right,
         QCircuit.seq_action, QCircuit.seq_action, QCircuit.seq_action,
         CNOTGate_basis_tensor 1 1, show (1 : Fin (2^1)) + 1 = 0 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, TdgGate_bit0,
         CNOTGate_basis_tensor 1 0, show (1 : Fin (2^1)) + 0 = 1 by decide,
         QCircuit.par_action_tensor, TGate_bit1,
         QState.smul_tensor_left, QState.tensor_smul_right, QState.smul_smul,
         QState.smul_scalar_congr (show (Complex.I : ℂ)
            = Complex.exp (Complex.I * Real.pi / 4)
              * Complex.exp (Complex.I * Real.pi / 4) from t_phase_double.symm)]

end

end QLean.Examples
