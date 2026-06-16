import QLean

namespace QLean.Examples

open QLean

noncomputable section

-- ── Hadamard transform circuit ────────────────────────────────────────────────

/-- The n-qubit Hadamard transform: H applied in parallel to every qubit.
    `hadamardTransform n : Circuit n` applies H to qubit n-1 (high) and recurses on 0..n-2 (low). -/
def hadamardTransform : (n : ℕ) → Circuit n
  | 0     => 1
  | n + 1 => hadamardTransform n + HGate

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- Every gate in the Hadamard transform is unitary, so the circuit is well-formed. -/
theorem wf_hadamardTransform (n : ℕ) : Circuit.WF (hadamardTransform n) := by
  induction n with
  | zero => simp [hadamardTransform]
  | succ n ih => simp [hadamardTransform, ih, isUnitary_H]

-- ── Uniform superposition state ───────────────────────────────────────────────

/-- The uniform superposition over all n-qubit basis states: amplitude 1/√(2^n) everywhere. -/
def uniformSuper (n : ℕ) : QVector n := fun _ _ => (Real.sqrt (2 ^ n : ℝ) : ℂ)⁻¹

-- ── Helper lemmas ──────────────────────────────────────────────────────────────

-- The all-zeros pair maps to index 0 under `tensorIndexEquiv`.
private lemma tensorIndexEquiv_zero_zero (j k : ℕ) :
    tensorIndexEquiv j k ⟨(0 : Fin (2 ^ j)), (0 : Fin (2 ^ k))⟩ = (0 : Fin (2 ^ (j + k))) := by
  have h : (tensorIndexEquiv j k).symm (0 : Fin (2 ^ (j + k))) =
      ⟨(0 : Fin (2 ^ j)), (0 : Fin (2 ^ k))⟩ :=
    Prod.ext
      (Fin.ext (by simp [tensorIndexEquiv_symm_fst_val]))
      (Fin.ext (by simp [tensorIndexEquiv_symm_snd_val]))
  calc tensorIndexEquiv j k ⟨0, 0⟩
      = tensorIndexEquiv j k ((tensorIndexEquiv j k).symm 0) := by rw [h]
    _ = 0 := (tensorIndexEquiv j k).apply_symm_apply 0

-- H maps |0⟩ to the uniform superposition over {|0⟩, |1⟩}.
private lemma H_ket_zero : H * ket (0 : Fin (2 ^ 1)) = uniformSuper 1 := by
  ext r s
  obtain rfl : s = 0 := Subsingleton.elim s 0
  fin_cases r <;>
  simp [Matrix.mul_apply, H, ket_apply, uniformSuper,
        Matrix.cons_val_zero, Matrix.cons_val_one, pow_one]

-- Tensor product of uniform superpositions is a uniform superposition.
private lemma tensorState_uniformSuper (n : ℕ) :
    tensorState (uniformSuper n) (uniformSuper 1) = uniformSuper (n + 1) := by
  funext i j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp only [tensorState_apply, uniformSuper, pow_one]
  -- Goal: (√(2^n) : ℂ)⁻¹ * (√2 : ℂ)⁻¹ = (√(2^(n+1)) : ℂ)⁻¹
  have hsqrt : Real.sqrt (2 ^ n : ℝ) * Real.sqrt 2 = Real.sqrt (2 ^ (n + 1) : ℝ) := by
    rw [pow_succ, Real.sqrt_mul (by positivity)]
  calc (Real.sqrt (2 ^ n : ℝ) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹
      = ((Real.sqrt (2 ^ n : ℝ) : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ := by
          rw [mul_inv_rev]; exact mul_comm _ _
    _ = ((↑(Real.sqrt (2 ^ n : ℝ) * Real.sqrt 2) : ℂ))⁻¹ := by
          rw [Complex.ofReal_mul]
    _ = (Real.sqrt (2 ^ (n + 1) : ℝ) : ℂ)⁻¹ := by rw [hsqrt]

-- ── Main theorem ──────────────────────────────────────────────────────────────

/-- The n-qubit Hadamard transform prepares the uniform superposition:
    each of the 2^n basis states gets amplitude 1/√(2^n). -/
theorem hadamardTransform_prepares (n : ℕ) : (hadamardTransform n).prepares (uniformSuper n) := by
  simp only [Circuit.maps_iff]
  induction n with
  | zero =>
    simp only [hadamardTransform, eval_id, Matrix.one_mul]
    ext r s
    obtain rfl : s = 0 := Subsingleton.elim s 0
    fin_cases r
    simp [ket_apply, uniformSuper, pow_zero, Real.sqrt_one]
  | succ n ih =>
    simp only [hadamardTransform, eval_par, eval_gate]
    -- Rewrite ket 0 : Fin (2^(n+1)) as ket (tensorIndexEquiv n 1 ⟨0, 0⟩)
    rw [show (0 : Fin (2 ^ (n + 1))) = tensorIndexEquiv n 1 ⟨0, 0⟩ from
          (tensorIndexEquiv_zero_zero n 1).symm]
    -- Split the kronecker product action across the tensor-product index
    rw [kron_mul_ket]
    -- Apply the inductive hypothesis and the single-qubit H action
    rw [ih, H_ket_zero]
    exact tensorState_uniformSuper n

end

end QLean.Examples
