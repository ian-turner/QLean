import QLean

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

-- ── Hadamard transform circuit ────────────────────────────────────────────────

/-- The n-qubit Hadamard transform: H applied in parallel to every qubit.
    `hadamardTransform n : QCircuit n` applies H to qubit n-1 (high) and recurses on 0..n-2 (low). -/
def hadamardTransform : (n : ℕ) → QCircuit n
  | 0     => 1
  | n + 1 => hadamardTransform n ⊗ HGate

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- Every gate in the Hadamard transform is unitary, so the circuit is well-formed. -/
theorem wf_hadamardTransform (n : ℕ) : QCircuit.WF (hadamardTransform n) := by
  induction n with
  | zero => simp [hadamardTransform]
  | succ n ih => simp [hadamardTransform, ih, isUnitary_H]

-- ── Uniform superposition state ───────────────────────────────────────────────

/-- The single-qubit uniform superposition `|+⟩ = (❘0⟩ + ❘1⟩)/√2`, as a symbolic state.
    Exactly the right-hand side of `HGate_bit0`. -/
def plusState : QState 1 := ((Real.sqrt 2)⁻¹ : ℂ) • (❘0⟩ + ❘1⟩)

/-- The n-qubit uniform superposition as a symbolic state: a tensor power of `plusState`,
    one `|+⟩` factor per qubit. `uniformSuperState 0` is the empty ket `❘0⟩ : QState 0`. -/
def uniformSuperState : (n : ℕ) → QState n
  | 0     => ❘0⟩
  | n + 1 => uniformSuperState n ⊗ plusState

-- ── Main theorem ──────────────────────────────────────────────────────────────

/-- The n-qubit Hadamard transform sends the all-zeros ket to the uniform superposition.

    By induction on `n`: split the input as `❘0⟩ ≈ ❘0⟩ ⊗ ❘0⟩`, act componentwise on the
    tensor, rewrite the low `n` qubits by the inductive hypothesis and the high qubit by
    `HGate_bit0`. The result `uniformSuperState n ⊗ plusState` is `uniformSuperState (n+1)`. -/
theorem hadamardTransform_prepares (n : ℕ) :
    hadamardTransform n * (❘0⟩ : QState n) ≈ uniformSuperState n := by
  induction n with
  | zero =>
    simp only [hadamardTransform, uniformSuperState]
    grw [QCircuit.id_action]
  | succ n ih =>
    simp only [hadamardTransform, uniformSuperState, plusState]
    grw [QState.ket_zero_tensor n 1, QCircuit.par_action_tensor, ih, HGate_bit0]

end

end QLean.Examples
