import QLean

/-!
# SWAP from three CNOTs

`SWAP = CNOT · CNOT-reversed · CNOT` (N&C Figure 1.7, eq. 1.20; Fenner Ex 11.2): the
classic three-XOR trick `(a,b) ↦ (a, a⊕b) ↦ (b, a⊕b) ↦ (b, a)` at the circuit level.

Proved on factored basis states via `Equiv.basis_iff_tensor` and the CNOT/CNOTRev tensor
actions; the leftover `Fin 2` index arithmetic (`a + (a + b) = b`) is discharged by
`decide` after a case split.
-/

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

/-- SWAP as three alternating CNOTs (rightmost acts first). -/
theorem swap_three_cnot : CNOTGate * CNOTRevGate * CNOTGate ≈ SWAPGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_basis_tensor,
       CNOTRevGate_basis_tensor, CNOTGate_basis_tensor, SWAPGate_tensor,
       show a + (a + b) = b by fin_cases a <;> fin_cases b <;> decide,
       show b + (a + b) = a by fin_cases a <;> fin_cases b <;> decide]

/-- SWAP is an involution — a corollary at the level of arbitrary symbolic product
    states, no basis reduction needed. -/
theorem swap_mul_swap : SWAPGate * SWAPGate ≈ (1 : QCircuit (1 + 1)) := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, SWAPGate_tensor, SWAPGate_tensor, QCircuit.id_action]

end

end QLean.Examples
