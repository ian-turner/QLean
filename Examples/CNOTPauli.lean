import QLean

/-!
# CNOT–Pauli conjugation table

How CNOT conjugation propagates Pauli operators (N&C Exercise 4.31, eqs. 4.32–4.37) —
the algebra behind stabilizer/Gottesman–Knill bookkeeping. With `C = CNOT` (control =
qubit 0 = low tensor factor, target = qubit 1):

| conjugated | result |
|---|---|
| `C (X⊗1) C` | `X ⊗ X` |
| `C (Y⊗1) C` | `Y ⊗ X` |
| `C (Z⊗1) C` | `Z ⊗ 1` |
| `C (1⊗X) C` | `1 ⊗ X` |
| `C (1⊗Y) C` | `Z ⊗ Y` |
| `C (1⊗Z) C` | `Z ⊗ Z` |

All proofs reduce to factored basis states; X/Z cases use the uniform phase-form atoms
(`XGate_basis`, `ZGate_basis`) with the `Fin 2` index arithmetic discharged by `decide`,
while the Y cases split on the control bit.
-/

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

local notation "id1" => (1 : QCircuit 1)

/-- `C (X⊗1) C ≈ X ⊗ X`: an X on the control copies onto the target. -/
theorem cnot_conj_x_control :
    CNOTGate * (XGate ⊗ id1) * CNOTGate ≈ XGate ⊗ XGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor,
       QCircuit.par_action_tensor, QCircuit.id_action, XGate_basis,
       CNOTGate_basis_tensor, QCircuit.par_action_tensor, XGate_basis, XGate_basis,
       show a + 1 + (a + b) = b + 1 by fin_cases a <;> fin_cases b <;> decide]

/-- `C (Z⊗1) C ≈ Z ⊗ 1`: a Z on the control commutes straight through. -/
theorem cnot_conj_z_control :
    CNOTGate * (ZGate ⊗ id1) * CNOTGate ≈ ZGate ⊗ id1 := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor,
       QCircuit.par_action_tensor, QCircuit.id_action, ZGate_basis,
       QState.smul_tensor_left, QCircuit.apply_smul, CNOTGate_basis_tensor,
       QCircuit.par_action_tensor, QCircuit.id_action, ZGate_basis,
       QState.smul_tensor_left,
       show a + (a + b) = b by fin_cases a <;> fin_cases b <;> decide]

/-- `C (1⊗X) C ≈ 1 ⊗ X`: an X on the target commutes straight through. -/
theorem cnot_conj_x_target :
    CNOTGate * (id1 ⊗ XGate) * CNOTGate ≈ id1 ⊗ XGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor,
       QCircuit.par_action_tensor, QCircuit.id_action, XGate_basis,
       CNOTGate_basis_tensor, QCircuit.par_action_tensor, QCircuit.id_action, XGate_basis,
       show a + (a + b + 1) = b + 1 by fin_cases a <;> fin_cases b <;> decide]

/-- `C (1⊗Z) C ≈ Z ⊗ Z`: a Z on the target copies onto the control. -/
theorem cnot_conj_z_target :
    CNOTGate * (id1 ⊗ ZGate) * CNOTGate ≈ ZGate ⊗ ZGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor,
       QCircuit.par_action_tensor, QCircuit.id_action, ZGate_basis,
       QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor,
       QCircuit.par_action_tensor, ZGate_basis, ZGate_basis,
       QState.smul_tensor_left, QState.tensor_smul_right, QState.smul_smul,
       show a + (a + b) = b by fin_cases a <;> fin_cases b <;> decide,
       QState.smul_scalar_congr (show ((-1 : ℂ)) ^ (a + b).val
          = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val by
            fin_cases a <;> fin_cases b <;> norm_num [Fin.val_add])]

/-- `C (Y⊗1) C ≈ Y ⊗ X`: a Y on the control propagates an X onto the target. -/
theorem cnot_conj_y_control :
    CNOTGate * (YGate ⊗ id1) * CNOTGate ≈ YGate ⊗ XGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor,
         QCircuit.par_action_tensor, QCircuit.id_action, YGate_bit0,
         QState.smul_tensor_left, QCircuit.apply_smul, CNOTGate_basis_tensor,
         QCircuit.par_action_tensor, YGate_bit0, XGate_basis, QState.smul_tensor_left,
         show (0 : Fin (2^1)) + b = b from zero_add b,
         show (1 : Fin (2^1)) + b = b + 1 by fin_cases b <;> decide]
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor,
         QCircuit.par_action_tensor, QCircuit.id_action, YGate_bit1,
         QState.smul_tensor_left, QCircuit.apply_smul, CNOTGate_basis_tensor,
         QCircuit.par_action_tensor, YGate_bit1, XGate_basis, QState.smul_tensor_left,
         show (0 : Fin (2^1)) + (1 + b) = b + 1 by fin_cases b <;> decide]

/-- `C (1⊗Y) C ≈ Z ⊗ Y`: a Y on the target propagates a Z onto the control. -/
theorem cnot_conj_y_target :
    CNOTGate * (id1 ⊗ YGate) * CNOTGate ≈ ZGate ⊗ YGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor 0 0,
         show (0 : Fin (2^1)) + 0 = 0 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, YGate_bit0,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 0 1,
         show (0 : Fin (2^1)) + 1 = 1 by decide,
         QCircuit.par_action_tensor, ZGate_bit0, YGate_bit0, QState.tensor_smul_right]
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor 0 1,
         show (0 : Fin (2^1)) + 1 = 1 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, YGate_bit1,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 0 0,
         show (0 : Fin (2^1)) + 0 = 0 by decide,
         QCircuit.par_action_tensor, ZGate_bit0, YGate_bit1, QState.tensor_smul_right]
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor 1 0,
         show (1 : Fin (2^1)) + 0 = 1 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, YGate_bit1,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 1 0,
         show (1 : Fin (2^1)) + 0 = 1 by decide,
         QCircuit.par_action_tensor, ZGate_bit1, YGate_bit0,
         QState.tensor_smul_right, QState.smul_tensor_left, QState.smul_smul]
    exact QState.smul_scalar_congr (by ring) _
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor 1 1,
         show (1 : Fin (2^1)) + 1 = 0 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, YGate_bit0,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 1 1,
         show (1 : Fin (2^1)) + 1 = 0 by decide,
         QCircuit.par_action_tensor, ZGate_bit1, YGate_bit1,
         QState.tensor_smul_right, QState.smul_tensor_left, QState.smul_smul]
    exact QState.smul_scalar_congr (by ring) _

end

end QLean.Examples
