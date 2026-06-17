import QLean

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

-- ── GHZ state preparation circuit ─────────────────────────────────────────────

/-- The GHZ preparation circuit on `n + 1` qubits.

    `ghzCircuit 0 = HGate` is a single Hadamard; each step adds one qubit and one
    CNOT, entangling the new top qubit (qubit `n + 1`) with the previous top qubit
    (qubit `n`):

    `ghzCircuit (n+1) = ((1 : QCircuit n) ⊗ CNOTGate) * (ghzCircuit n ⊗ (1 : QCircuit 1))`

    Indexed by the number of CNOTs `n`, so `ghzCircuit n : QCircuit (n + 1)` always
    acts on at least one qubit and `ghzCircuit 1` is exactly the Bell circuit. -/
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

/-- The `(n+1)`-qubit GHZ state `|GHZ⟩ = (|0…0⟩ + |1…1⟩)/√2`, as a symbolic state
    expression: an equal superposition of the all-zeros basis ket `❘0⟩` and the
    all-ones basis ket `❘allOnes (n+1)⟩`. Like the Bell state (the `n = 0` case after
    the first CNOT), it is maximally entangled — it does not factor as a tensor product
    of single-qubit states. The normalization is always `1/√2`: there are only ever two
    terms, regardless of the number of qubits. -/
def ghzState (n : ℕ) : QState (n + 1) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (❘0⟩ + ❘allOnes (n + 1)⟩)

-- ── Main theorem ──────────────────────────────────────────────────────────────

/-- The GHZ circuit sends the all-zeros ket to the GHZ state.

    Equational reasoning in the symbolic state layer, by induction on `n`.

    * **Base case** (`n = 0`): a single Hadamard, `HGate_bit0` turns `❘0⟩` into
      `(❘0⟩ + ❘1⟩)/√2 = ghzState 0` (since `allOnes 1 = 1`).

    * **Inductive step**: peel the new top qubit off the input (`ket_zero_tensor`),
      run `ghzCircuit n` on the low qubits via the inductive hypothesis and the
      identity on the new qubit (`par_action_tensor`, `id_action`), leaving
      `ghzState n ⊗ ❘0⟩`. Distribute the tensor over the superposition
      (`smul_tensor_left`, `add_tensor_left`) and **re-associate** each term so the
      previous top qubit and the new qubit form an adjacent pair (`ket_zero_tensor`,
      `allOnes_succ`, `tensor_assoc`) — the step the Hadamard transform and Bell
      examples never needed, because GHZ's CNOT straddles the tensor boundary. The
      final CNOT (`1 ⊗ CNOTGate`) then acts on that pair (`apply_smul`, `apply_add`,
      `par_action_tensor`, `CNOTGate_basis_tensor`), copying the control bit onto the
      new qubit: `❘0⟩ ⊗ ❘0⟩ ↦ ❘0⟩ ⊗ ❘0⟩` extends the all-zeros run and
      `❘1⟩ ⊗ ❘0⟩ ↦ ❘1⟩ ⊗ ❘1⟩` extends the all-ones run. A final `gcongr` matches the
      result against `ghzState (n+1)` by re-expanding its two basis kets. -/
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
