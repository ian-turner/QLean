import QLean

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

-- ── Bell state preparation circuit ────────────────────────────────────────────

/-- The Bell-state preparation circuit on two qubits (`QCircuit (1 + 1) = QCircuit 2`):
    a Hadamard on qubit 0 followed by a CNOT with control qubit 0, target qubit 1.
    In matrix order the rightmost factor acts first, so `CNOTGate * (HGate ⊗ 1)` runs
    `H ⊗ 1` first. -/
def bellCircuit : QCircuit (1 + 1) := CNOTGate * (HGate ⊗ (1 : QCircuit 1))

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- Every gate in the Bell circuit is unitary, so the circuit is well-formed. -/
theorem wf_bellCircuit : QCircuit.WF bellCircuit := by
  simp [bellCircuit, isUnitary_H, isUnitary_CNOT]

-- ── Bell state ────────────────────────────────────────────────────────────────

/-- The Bell state `|Φ⁺⟩ = (❘00⟩ + ❘11⟩)/√2`, as a symbolic state expression.
    Entangled: it does not factor as a tensor product of single-qubit states. -/
def bellState : QState (1 + 1) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (❘0⟩ ⊗ ❘0⟩ + ❘1⟩ ⊗ ❘1⟩)

-- ── Main theorem ──────────────────────────────────────────────────────────────

/-- The Bell circuit sends the all-zeros ket `❘00⟩` to the Bell state `|Φ⁺⟩`.

    A single `grw` chain: apply `H ⊗ 1` first (`HGate_bit0` puts the low qubit in
    superposition), distribute the scalar and sum out through the tensor, then let the
    CNOT flip the target on each basis tensor (`CNOTGate_basis_tensor`), yielding
    `(❘00⟩ + ❘11⟩)/√2`. -/
theorem bellCircuit_prepares :
    bellCircuit * (❘0⟩ : QState (1 + 1)) ≈ bellState := by
  simp only [bellCircuit, bellState]
  grw [QCircuit.seq_action, QState.ket_zero_tensor 1 1, QCircuit.par_action_tensor,
       HGate_bit0, QCircuit.id_action, QState.smul_tensor_left, QState.add_tensor_left,
       QCircuit.apply_smul, QCircuit.apply_add, CNOTGate_basis_tensor 0 0,
       CNOTGate_basis_tensor 1 0]
  -- `CNOTGate_basis_tensor` leaves the targets as `❘0 + 0⟩` and `❘1 + 0⟩`;
  -- these are `❘0⟩` and `❘1⟩` definitionally, so `rfl` (via `QState.Equiv.refl`) closes it.
  rfl

end

end QLean.Examples
