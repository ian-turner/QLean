import QLean

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

-- ── GHZ state preparation circuit ─────────────────────────────────────────────

/-- The GHZ preparation circuit on `n + 1` qubits: `ghzCircuit 0` is a single Hadamard,
    and each step adds one qubit and a CNOT entangling the new top qubit with the previous
    one. Indexed by the CNOT count `n`, so `ghzCircuit n : QCircuit (n + 1)` and
    `ghzCircuit 1` is exactly the Bell circuit. -/
def ghzCircuit : (n : ℕ) → QCircuit (n + 1)
  | 0     => HGate
  | n + 1 => ((1 : QCircuit n) ⊗ CNOTGate) * (ghzCircuit n ⊗ (1 : QCircuit 1))

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- Every gate in the GHZ circuit is unitary, so the circuit is well-formed. -/
theorem wf_ghzCircuit (n : ℕ) : QCircuit.WF (ghzCircuit n) := by
  induction n with
  | zero => simp [ghzCircuit, isUnitary_H]
  | succ n ih => simp [ghzCircuit, ih, isUnitary_CNOT]

-- ── GHZ state ─────────────────────────────────────────────────────────────────

/-- The `(n+1)`-qubit GHZ state `|GHZ⟩ = (|0…0⟩ + |1…1⟩)/√2`, as a symbolic state: an equal
    superposition of the all-zeros ket `❘0⟩` and the all-ones ket `❘allOnes (n+1)⟩`. Maximally
    entangled, and always normalized by `1/√2` — there are only ever two terms. -/
def ghzState (n : ℕ) : QState (n + 1) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (❘0⟩ + ❘allOnes (n + 1)⟩)

-- ── Main theorem ──────────────────────────────────────────────────────────────

/-- The GHZ circuit sends the all-zeros ket to the GHZ state, by induction on `n`.

    * **Base case** (`n = 0`): a single Hadamard, `HGate_bit0` turns `❘0⟩` into
      `(❘0⟩ + ❘1⟩)/√2 = ghzState 0`.

    * **Inductive step**: peel the new top qubit off the input, run `ghzCircuit n` on the
      low qubits via the inductive hypothesis, then re-associate so the previous and new
      top qubits form an adjacent pair. The final CNOT copies the control bit onto
      the new qubit, extending both the all-zeros and all-ones runs. -/
theorem ghzCircuit_prepares (n : ℕ) :
    ghzCircuit n * (❘0⟩ : QState (n + 1)) ≈ ghzState n := by
  induction n with
  | zero =>
    simp only [ghzCircuit, ghzState]
    grw [HGate_bit0]
    rfl
  | succ n ih =>
    simp only [ghzCircuit]
    grw [QCircuit.seq_action, QState.ket_zero_tensor (n + 1) 1,
         QCircuit.par_action_tensor, ih, QCircuit.id_action]
    simp only [ghzState]
    grw [QState.smul_tensor_left, QState.add_tensor_left,
         QState.ket_zero_tensor n 1, QState.allOnes_succ n,
         QState.tensor_assoc, QState.tensor_assoc,
         QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.par_action_tensor, QCircuit.par_action_tensor,
         QCircuit.id_action, QCircuit.id_action,
         CNOTGate_basis_tensor 0 0, CNOTGate_basis_tensor 1 0]
    -- `CNOTGate_basis_tensor` leaves the targets as `❘0 + 0⟩`/`❘1 + 0⟩`; normalize them.
    simp only [add_zero]
    -- LHS is now `(√2)⁻¹ • (❘0⟩ ⊗ (❘0⟩ ⊗ ❘0⟩) + ❘allOnes n⟩ ⊗ (❘1⟩ ⊗ ❘1⟩))`;
    -- match it against `ghzState (n+1)` by re-expanding its two basis kets.
    gcongr
    · grw [QState.ket_zero_tensor n 2, QState.ket_zero_tensor 1 1]
    · grw [QState.allOnes_succ (n + 1), QState.allOnes_succ n, QState.tensor_assoc]

end

end QLean.Examples
