import QLean

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

-- ── Bell state preparation circuit ────────────────────────────────────────────

/-- The Bell-state preparation circuit on two qubits (`QCircuit (1 + 1) = QCircuit 2`):
    a Hadamard on qubit 0 (the low qubit) followed by a CNOT with control qubit 0
    and target qubit 1.

    `HGate ⊗ (1 : QCircuit 1)` runs H on the low qubit and the identity on the high
    qubit; in matrix order the rightmost factor acts first, so `CNOTGate * (HGate ⊗ 1)`
    runs `H ⊗ 1` first and the CNOT afterwards. -/
def bellCircuit : QCircuit (1 + 1) := CNOTGate * (HGate ⊗ (1 : QCircuit 1))

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- Every gate in the Bell circuit is unitary, so the circuit is well-formed. -/
theorem wf_bellCircuit : QCircuit.WF bellCircuit := by
  simp [bellCircuit, isUnitary_H, isUnitary_CNOT]

-- ── Bell state ────────────────────────────────────────────────────────────────

/-- The Bell state `|Φ⁺⟩ = (❘00⟩ + ❘11⟩)/√2`, as a symbolic state expression.

    Unlike `uniformSuperState` in the Hadamard-transform example, this state is
    *entangled*: it does not factor as a tensor product of single-qubit states. -/
def bellState : QState (1 + 1) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (❘0⟩ ⊗ ❘0⟩ + ❘1⟩ ⊗ ❘1⟩)

-- ── Main theorem ──────────────────────────────────────────────────────────────

/-- The Bell circuit sends the all-zeros ket `❘00⟩` to the Bell state `|Φ⁺⟩`.

    Equational reasoning in the symbolic state layer, like the other examples, with a
    single `grw` chain (`rw` modulo `≈`, descending under the tensor/apply/smul/add
    congruences automatically):

    * `QCircuit.seq_action` reorders to "apply `HGate ⊗ 1`, then `CNOTGate`".
    * Split the input `❘0⟩ ≈ ❘0⟩ ⊗ ❘0⟩` (`QState.ket_zero_tensor`) and act
      componentwise (`QCircuit.par_action_tensor`): `HGate_bit0` turns the low qubit
      into `(❘0⟩ + ❘1⟩)/√2`, while `QCircuit.id_action` leaves the high qubit at `❘0⟩`.
    * Push the resulting scalar and sum out through the tensor and the remaining
      `CNOTGate` (`QState.smul_tensor_left`, `QState.add_tensor_left`,
      `QCircuit.apply_smul`, `QCircuit.apply_add`), so the CNOT lands on each basis
      tensor separately.
    * `CNOTGate_basis_tensor` flips the target: `❘0⟩ ⊗ ❘0⟩ ↦ ❘0⟩ ⊗ ❘0⟩` and
      `❘1⟩ ⊗ ❘0⟩ ↦ ❘1⟩ ⊗ ❘1⟩`, giving `(❘00⟩ + ❘11⟩)/√2 = bellState`. -/
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
