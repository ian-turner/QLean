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
    This is exactly the right-hand side of `HGate_bit0`, so `H` applied to `❘0⟩` is `≈ plusState`. -/
def plusState : QState 1 := ((Real.sqrt 2)⁻¹ : ℂ) • ((❘0⟩ : QState 1) + ❘1⟩)

/-- The n-qubit uniform superposition as a symbolic state: a tensor power of `plusState`,
    one `|+⟩` factor per qubit. `uniformSuperState 0` is the empty ket `❘0⟩ : QState 0`. -/
def uniformSuperState : (n : ℕ) → QState n
  | 0     => ❘0⟩
  | n + 1 => uniformSuperState n ⊗ plusState

-- ── Main theorem ──────────────────────────────────────────────────────────────

/-- The n-qubit Hadamard transform sends the all-zeros ket to the uniform superposition.

    The argument is equational reasoning in the symbolic state layer, mirroring `rz_commutes_cnot`.
    By induction on `n`, with `grw` (`rw` modulo `≈`, descending under the tensor/apply
    congruences automatically) driving the inductive step:

    * Split the all-zeros input as `❘0⟩ ≈ ❘0⟩ ⊗ ❘0⟩` (`QState.ket_zero_tensor`).
    * `hadamardTransform n ⊗ HGate` acts componentwise on the tensor (`QCircuit.par_action_tensor`).
    * The inductive hypothesis rewrites the low `n` qubits to `uniformSuperState n`.
    * `HGate_bit0` rewrites the high qubit `HGate * ❘0⟩` to `plusState`.

    The result is `uniformSuperState n ⊗ plusState`, which is `uniformSuperState (n+1)` by definition. -/
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
