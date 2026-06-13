import QLean.Basic.PiLp

open scoped Matrix InnerProductSpace

noncomputable section

namespace QLean

-- ── Normalization predicate ───────────────────────────────────────────────────

/-- A quantum state is normalized if it has unit norm. Analogous to `IsUnitary` for gates. -/
def IsNormalized {n : ℕ} (ψ : QState n) : Prop := ‖ψ‖ = 1

-- ── Computational basis ───────────────────────────────────────────────────────

/-- The `i`-th computational basis state: amplitude 1 at index `i`, 0 elsewhere. -/
def ket {n : ℕ} (i : Fin (2^n)) : QState n := EuclideanSpace.single i 1

/-- Coordinate of a basis state (`.ofLp` form, for use in norm/inner product lemmas). -/
@[simp] theorem ket_ofLp {n : ℕ} (i j : Fin (2^n)) :
    (ket i).ofLp j = if j = i then 1 else 0 := by
  simp [ket, PiLp.single_apply]

theorem ket_normalized {n : ℕ} (i : Fin (2^n)) : IsNormalized (ket i) := by
  simp [IsNormalized, ket, PiLp.norm_single]

theorem ket_inner {n : ℕ} (i j : Fin (2^n)) :
    @inner ℂ _ _ (ket i) (ket j) = if i = j then 1 else 0 := by
  simp [ket, EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem ket_orthonormal {n : ℕ} : Orthonormal ℂ (ket (n := n)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [ket, EuclideanSpace.inner_single_left, PiLp.single_apply]

-- ── Tensor product of states ──────────────────────────────────────────────────

/-- Tensor product of a `j`-qubit state and a `k`-qubit state.
    Index `i : Fin (2^(j+k))` decomposes via `tensorIndexEquiv` as `(low j bits, high k bits)`. -/
def tensorState {j k : ℕ} (ψ : QState j) (φ : QState k) : QState (j+k) :=
  QState.ofFun (fun i =>
    ψ.ofLp ((tensorIndexEquiv j k).symm i).1 *
    φ.ofLp ((tensorIndexEquiv j k).symm i).2)

/-- `.ofLp` projection of a tensor product state (the form needed by norm/inner product lemmas). -/
@[simp] theorem tensorState_ofLp {j k : ℕ} (ψ : QState j) (φ : QState k)
    (i : Fin (2^(j+k))) :
    (tensorState ψ φ).ofLp i =
    ψ.ofLp ((tensorIndexEquiv j k).symm i).1 *
    φ.ofLp ((tensorIndexEquiv j k).symm i).2 := by
  simp [tensorState, QState.ofFun]

/-- Tensor product of basis states is the basis state at the combined index. -/
theorem ket_tensorState {j k : ℕ} (a : Fin (2^j)) (b : Fin (2^k)) :
    tensorState (ket a) (ket b) = ket (tensorIndexEquiv j k ⟨a, b⟩) := by
  apply (WithLp.equiv 2 (Fin (2^(j+k)) → ℂ)).injective
  simp only [WithLp.equiv_apply]
  funext i
  simp only [tensorState_ofLp, ket_ofLp]
  rcases eq_or_ne ((tensorIndexEquiv j k).symm i) ⟨a, b⟩ with h | h
  · -- Positive case: the index matches
    have hi : i = tensorIndexEquiv j k ⟨a, b⟩ := (Equiv.symm_apply_eq _).mp h
    subst hi; simp
  · -- Negative case: the index does not match → product is 0
    have hi : i ≠ tensorIndexEquiv j k ⟨a, b⟩ := by
      intro heq; exact h (by simp [heq])
    rw [if_neg hi]
    have hprod : ¬(((tensorIndexEquiv j k).symm i).1 = a ∧ ((tensorIndexEquiv j k).symm i).2 = b) :=
      fun ⟨h1, h2⟩ => h (Prod.ext h1 h2)
    push Not at hprod
    by_cases h1 : ((tensorIndexEquiv j k).symm i).1 = a
    · simp [h1, hprod h1]
    · simp [h1]

-- ── Normalization of tensor products ─────────────────────────────────────────

private theorem tensorState_norm_sq {j k : ℕ} (ψ : QState j) (φ : QState k) :
    ∑ i : Fin (2^(j+k)), ‖(tensorState ψ φ).ofLp i‖^2 =
    (∑ a : Fin (2^j), ‖ψ.ofLp a‖^2) * (∑ b : Fin (2^k), ‖φ.ofLp b‖^2) := by
  simp_rw [tensorState_ofLp, norm_mul, mul_pow]
  -- Reindex from Fin (2^(j+k)) to Fin (2^j) × Fin (2^k)
  rw [Fintype.sum_equiv (tensorIndexEquiv j k).symm _ (fun p => ‖ψ.ofLp p.1‖^2 * ‖φ.ofLp p.2‖^2)
      (fun _ => rfl)]
  -- Factor the product sum
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Tensor product of normalized states is normalized. -/
theorem IsNormalized.tensorState {j k : ℕ} {ψ : QState j} {φ : QState k}
    (hψ : IsNormalized ψ) (hφ : IsNormalized φ) : IsNormalized (tensorState ψ φ) := by
  unfold IsNormalized
  rw [EuclideanSpace.norm_eq, tensorState_norm_sq]
  -- Express each factor as the norm squared
  have norm_sq {m : ℕ} (v : QState m) (hv : IsNormalized v) :
      ∑ i : Fin (2^m), ‖v.ofLp i‖^2 = 1 := by
    have h : Real.sqrt (∑ i : Fin (2^m), ‖v.ofLp i‖^2) = 1 := by
      rw [← EuclideanSpace.norm_eq]; exact hv
    have hnn : (0:ℝ) ≤ ∑ i : Fin (2^m), ‖v.ofLp i‖^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    calc ∑ i : Fin (2^m), ‖v.ofLp i‖^2
        = (Real.sqrt (∑ i : Fin (2^m), ‖v.ofLp i‖^2))^2 := (Real.sq_sqrt hnn).symm
      _ = 1^2 := by rw [h]
      _ = 1 := one_pow 2
  rw [norm_sq ψ hψ, norm_sq φ hφ, mul_one, Real.sqrt_one]

end QLean

end
