import QLean
import Mathlib.Algebra.Ring.GeomSum

namespace QLean.Examples

open QLean

noncomputable section

-- ── QFT output state ──────────────────────────────────────────────────────────

/-- The n-qubit QFT output for input |j⟩: amplitude at basis state |k⟩ is
    e^{2πijk/2^n} / √(2^n), implementing the discrete Fourier transform. -/
def qftState (n : ℕ) (j : Fin (2^n)) : QState n :=
  fun k _ => (Real.sqrt (2^n : ℝ) : ℂ)⁻¹ *
             Complex.exp (2 * Real.pi * Complex.I * j.val * k.val / 2^n)

-- ── QFT matrix ────────────────────────────────────────────────────────────────

/-- The n-qubit Quantum Fourier Transform: a 2^n × 2^n unitary implementing the DFT.
    Entry (k, j) is e^{2πijk/N}/√N where N = 2^n; columns are the qftState outputs. -/
def qftMatrix (n : ℕ) : QMatrix n :=
  fun k j => (Real.sqrt (2^n : ℝ) : ℂ)⁻¹ *
             Complex.exp (2 * Real.pi * Complex.I * k.val * j.val / 2^n)

-- ── Unitarity helpers ─────────────────────────────────────────────────────────

-- (√(2^n))⁻¹ * (√(2^n))⁻¹ * 2^n = 1
private lemma inv_sqrt_sq_mul (n : ℕ) :
    ((Real.sqrt (2^n : ℝ) : ℂ)⁻¹ * (Real.sqrt (2^n : ℝ) : ℂ)⁻¹) * (2^n : ℝ) = 1 := by
  have hpos : (0 : ℝ) < 2^n := by positivity
  have hsq : (Real.sqrt (2^n : ℝ) : ℂ) ^ 2 = (2^n : ℝ) := by
    have : Real.sqrt (2^n : ℝ) ^ 2 = (2^n : ℝ) := Real.sq_sqrt hpos.le
    exact_mod_cast this
  rw [show ((Real.sqrt (2^n : ℝ) : ℂ)⁻¹ * (Real.sqrt (2^n : ℝ) : ℂ)⁻¹) =
          ((Real.sqrt (2^n : ℝ) : ℂ) ^ 2)⁻¹ from by rw [← sq, inv_pow], hsq]
  exact inv_mul_cancel₀ (by exact_mod_cast hpos.ne')

-- exp(2πi * m * k / N) = exp(2πim/N)^k.val, i.e., is a power of a root of unity.
private lemma exp_mul_eq_pow (n : ℕ) (m : ℤ) (k : Fin (2^n)) :
    Complex.exp (2 * Real.pi * Complex.I * m * k.val / 2^n) =
    Complex.exp (2 * Real.pi * Complex.I * m / 2^n) ^ k.val := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

-- exp(2πim) = 1 for any integer m.
private lemma exp_int_mul_two_pi_I (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * m) = 1 := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show 2 * ↑Real.pi * Complex.I * (↑k + 1) =
            2 * ↑Real.pi * Complex.I * ↑k + 2 * ↑Real.pi * Complex.I from by ring,
        Complex.exp_add, ih, one_mul, Complex.exp_two_pi_mul_I]
  | pred k ih =>
    push_cast at ih ⊢
    rw [show 2 * ↑Real.pi * Complex.I * (-(↑k : ℂ) - 1) =
            2 * ↑Real.pi * Complex.I * (-(↑k : ℂ)) + -(2 * ↑Real.pi * Complex.I) from by ring,
        Complex.exp_add, ih, one_mul, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

-- exp(2πim/2^n)^(2^n) = 1.
private lemma exp_frac_pow (n : ℕ) (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * m / 2^n) ^ (2^n) = 1 := by
  rw [← Complex.exp_nat_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ℂ)^n * (2 * ↑Real.pi * Complex.I * ↑m / (2 : ℂ)^n) =
           ↑m * (2 * ↑Real.pi * Complex.I) from by field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I m

-- The key non-vanishing lemma: exp(2πim/N) ≠ 1 when 0 < m.natAbs < N.
private lemma exp_frac_ne_one (n : ℕ) (m : ℤ)
    (hm0 : m ≠ 0) (hm : m.natAbs < 2^n) :
    Complex.exp (2 * Real.pi * Complex.I * m / 2^n) ≠ 1 := by
  rw [show (2 * Real.pi * Complex.I * ↑m / ↑(2^n) : ℂ) =
          ↑(2 * Real.pi * (m : ℝ) / 2^n) * Complex.I from by push_cast; ring]
  intro h
  set θ := 2 * Real.pi * (m : ℝ) / 2^n with hθ
  have hcos : Real.cos θ = 1 := by
    have h1 : (Complex.exp (↑θ * Complex.I)).re = 1 := by rw [h]; simp
    rw [Complex.exp_mul_I] at h1
    simp only [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im,
               Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at h1
    linarith
  rw [Real.cos_eq_one_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hN : (0 : ℝ) < 2^n := by positivity
  have hkm_real : (k : ℝ) * 2^n = m := by
    have h2 : (k : ℝ) * 2^n * (2 * Real.pi) = m * (2 * Real.pi) := by
      calc (k : ℝ) * 2^n * (2 * Real.pi)
          = k * (2 * Real.pi) * 2^n := by ring
        _ = θ * 2^n := by rw [hk]
        _ = 2 * Real.pi * m / 2^n * 2^n := rfl
        _ = m * (2 * Real.pi) := by field_simp [hN.ne']
    exact mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h2
  have hkm_int : k * (2^n : ℤ) = m := by exact_mod_cast hkm_real
  have hk0 : k = 0 := by
    by_contra hk_ne
    have h1k : 1 ≤ k.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk_ne)
    have habs := congr_arg Int.natAbs hkm_int
    simp only [Int.natAbs_mul, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl] at habs
    have hineq : 2^n ≤ m.natAbs := calc
      2^n = 1 * 2^n := (one_mul _).symm
      _ ≤ k.natAbs * 2^n := Nat.mul_le_mul_right _ h1k
      _ = m.natAbs := habs
    exact absurd hineq (Nat.not_le.mpr hm)
  rw [hk0, zero_mul] at hkm_int
  exact hm0 hkm_int.symm

-- ── Roots-of-unity orthogonality ──────────────────────────────────────────────

-- ∑ k : Fin N, exp(2πimk/N) = N if m ≡ 0 (mod N), else 0.
private lemma qft_phase_sum (n : ℕ) (i j : Fin (2^n)) :
    ∑ k : Fin (2^n), Complex.exp (2 * Real.pi * Complex.I * ((i : ℤ) - j) * k / 2^n) =
    if i = j then (2^n : ℂ) else 0 := by
  split_ifs with h
  · -- Diagonal: exponent = 0, all terms are 1
    subst h
    simp [Finset.sum_const, Complex.exp_zero]
  · -- Off-diagonal: geometric series
    set ω := Complex.exp (2 * Real.pi * Complex.I * ((i : ℤ) - j) / 2^n) with hω
    have hωN : ω ^ 2^n = 1 := by
      have hfp := exp_frac_pow n ((i : ℤ) - j)
      simp only [Int.cast_sub, Int.cast_natCast] at hfp
      exact hfp
    have hm0 : (i : ℤ) - j ≠ 0 := by
      intro heq; apply h; exact Fin.ext (by exact_mod_cast sub_eq_zero.mp heq)
    have hm_abs : ((i : ℤ) - j).natAbs < 2^n := by
      have hi : (i : ℤ) < 2^n := by exact_mod_cast i.isLt
      have hj : (j : ℤ) < 2^n := by exact_mod_cast j.isLt
      have hi0 : (0 : ℤ) ≤ i := Int.natCast_nonneg _
      have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg _
      omega
    have hω1 : ω ≠ 1 := by
      have hfne := exp_frac_ne_one n ((i : ℤ) - j) hm0 hm_abs
      simp only [Int.cast_sub, Int.cast_natCast] at hfne
      exact hfne
    -- Rewrite sum as ∑ k, ω^k using the geometric series formula
    have hpow : ∀ k : Fin (2^n),
        Complex.exp (2 * Real.pi * Complex.I * ((i : ℤ) - j) * k / 2^n) = ω ^ k.val := fun k => by
      rw [hω, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    simp_rw [hpow, Fin.sum_univ_eq_sum_range (fun k => ω ^ k)]
    -- Geometric series: (∑ ω^k) * (ω - 1) = ω^N - 1 = 0
    have hgeo : (∑ k ∈ Finset.range (2^n), ω ^ k) * (ω - 1) = ω ^ 2^n - 1 :=
      geom_sum_mul ω (2^n)
    rw [hωN, sub_self] at hgeo
    rcases mul_eq_zero.mp hgeo with hsum | h1
    · exact hsum
    · exact absurd (eq_of_sub_eq_zero h1) hω1

-- ── Unitarity ─────────────────────────────────────────────────────────────────

/-- The QFT matrix is unitary: columns are orthonormal by DFT orthogonality. -/
theorem isUnitary_qftMatrix (n : ℕ) : IsUnitary (qftMatrix n) := by
  unfold IsUnitary; ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, qftMatrix]
  have hstar_real : star (Real.sqrt (2^n : ℝ) : ℂ) = Real.sqrt (2^n : ℝ) := by
    rw [RCLike.star_def]; exact Complex.conj_ofReal _
  have hstar_exp : ∀ θ : ℝ, star (Complex.exp (↑θ * Complex.I)) = Complex.exp (-(↑θ * Complex.I)) := fun θ => by
    rw [RCLike.star_def, ← Complex.exp_conj]; congr 1
    simp only [(starRingEnd ℂ).map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  simp_rw [show ∀ k : Fin (2^n),
      (Real.sqrt (2^n : ℝ) : ℂ)⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ↑i * ↑k / ↑(2^n)) *
      star ((Real.sqrt (2^n : ℝ) : ℂ)⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑k / ↑(2^n))) =
      ((Real.sqrt (2^n : ℝ) : ℂ)⁻¹ * (Real.sqrt (2^n : ℝ) : ℂ)⁻¹) *
      Complex.exp (2 * Real.pi * Complex.I * ((i : ℤ) - j) * k / 2^n) from fun k => by
    set θ : ℝ := 2 * Real.pi * j.val * k.val / 2^n
    rw [show (2 * ↑Real.pi * Complex.I * ↑↑j * ↑↑k / ↑(2^n) : ℂ) = ↑θ * Complex.I from by
          simp [θ]; ring,
        star_mul, star_inv₀, hstar_real, hstar_exp θ,
        show (Real.sqrt (2^n : ℝ) : ℂ)⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ↑↑i * ↑↑k / ↑(2^n)) *
             (Complex.exp (-(↑θ * Complex.I)) * (Real.sqrt (2^n : ℝ) : ℂ)⁻¹) =
             ((Real.sqrt (2^n : ℝ) : ℂ)⁻¹ * (Real.sqrt (2^n : ℝ) : ℂ)⁻¹) *
             (Complex.exp (2 * ↑Real.pi * Complex.I * ↑↑i * ↑↑k / ↑(2^n)) *
              Complex.exp (-(↑θ * Complex.I))) from by ring,
        ← Complex.exp_add]
    congr 1; push_cast; simp [θ]; congr 1; ring]
  rw [← Finset.mul_sum, qft_phase_sum n i j]
  split_ifs with h
  · convert inv_sqrt_sq_mul n using 1; push_cast; ring
  · simp

-- ── QFT circuit gate ──────────────────────────────────────────────────────────

/-- The n-qubit QFT as a single circuit gate (the DFT unitary). -/
abbrev QFTGate (n : ℕ) : Circuit n := .gate (qftMatrix n)

/-- The QFT gate is well-formed: the DFT matrix is unitary. -/
@[simp] theorem wf_QFTGate (n : ℕ) : Circuit.WF (QFTGate n) :=
  isUnitary_qftMatrix n

-- ── Correctness ───────────────────────────────────────────────────────────────

/-- QFT applied to |j⟩ produces qftState n j: the DFT of the delta function at j. -/
theorem QFTGate_maps_ket (n : ℕ) (j : Fin (2^n)) :
    (QFTGate n).maps (ket j) (qftState n j) := by
  simp only [Circuit.maps_iff, eval_gate]
  ext k c; fin_cases c
  simp only [Matrix.mul_apply, qftMatrix, qftState, ket]
  simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1; congr 1; ring

/-- QFT on 1 qubit is the Hadamard gate: QFT₁ = H. -/
theorem qftMatrix_one_eq_H : qftMatrix 1 = H := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [qftMatrix, pow_one, Nat.cast_zero, Nat.cast_one,
               mul_zero, zero_div, Complex.exp_zero, mul_one] <;>
    simp [H]
  rw [show (2 * ↑Real.pi * Complex.I / 2 : ℂ) = ↑Real.pi * Complex.I from by ring,
      Complex.exp_pi_mul_I]
  ring

end

end QLean.Examples
