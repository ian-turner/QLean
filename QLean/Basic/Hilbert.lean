import QLean.Basic.Tensor
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Matrix

noncomputable section

namespace QLean

-- ── QState and action ─────────────────────────────────────────────────────────

/-- `n`-qubit quantum state: a column vector in `ℂ^(2^n)`. -/
abbrev QState (n : ℕ) := Matrix (Fin (2^n)) (Fin 1) ℂ

namespace QMatrix

/-- Act on a quantum state: matrix-vector multiplication as matrix multiplication. -/
def act {n : ℕ} (U : QMatrix n) (ψ : QState n) : QState n := U * ψ

@[simp] theorem act_def {n : ℕ} (U : QMatrix n) (ψ : QState n) : U.act ψ = U * ψ := rfl

theorem act_mul {n : ℕ} (U V : QMatrix n) (ψ : QState n) :
    QMatrix.act (U * V) ψ = U.act (V.act ψ) := by
  simp only [act_def, Matrix.mul_assoc]

theorem act_one {n : ℕ} (ψ : QState n) : (1 : QMatrix n).act ψ = ψ := by simp

end QMatrix

-- ── Normalization predicate ───────────────────────────────────────────────────

/-- A quantum state is normalized if the squared norms of its amplitudes sum to 1. -/
def IsNormalized {n : ℕ} (ψ : QState n) : Prop := ∑ i, ‖ψ i 0‖^2 = 1

-- ── Computational basis ───────────────────────────────────────────────────────

/-- The `i`-th computational basis state: amplitude 1 at row `i`, 0 elsewhere. -/
def ket {n : ℕ} (i : Fin (2^n)) : QState n := fun j _ => if j = i then 1 else 0

@[simp] theorem ket_apply {n : ℕ} (i j : Fin (2^n)) :
    ket i j 0 = if j = i then 1 else 0 := rfl

theorem ket_normalized {n : ℕ} (i : Fin (2^n)) : IsNormalized (ket i) := by
  unfold IsNormalized
  have key : ∀ j : Fin (2^n), ‖ket i j 0‖^2 = if j = i then 1 else 0 := by
    intro j; simp only [ket_apply]; split_ifs <;> simp
  simp_rw [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Inner product of basis states via the conjugate-transpose product. -/
theorem ket_inner {n : ℕ} (i j : Fin (2^n)) :
    ((ket i)ᴴ * ket j) 0 0 = if i = j then 1 else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ket_apply]
  by_cases h : i = j
  · subst h
    simp_rw [show ∀ k : Fin (2^n),
        star (if k = i then (1:ℂ) else 0) * (if k = i then 1 else 0) = if k = i then 1 else 0
        from fun k => by split_ifs <;> simp [star_one, star_zero]]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    rcases eq_or_ne k i with h1 | h1
    · subst h1; rw [if_pos rfl, star_one, if_neg h, mul_zero]
    · rw [if_neg h1, star_zero, zero_mul]

-- ── Tensor product of states ──────────────────────────────────────────────────

/-- Tensor product of a `j`-qubit state and a `k`-qubit state.
    Index `i : Fin (2^(j+k))` decomposes via `tensorIndexEquiv` as `(low j bits, high k bits)`. -/
def tensorState {j k : ℕ} (ψ : QState j) (φ : QState k) : QState (j+k) :=
  fun i _ => ψ ((tensorIndexEquiv j k).symm i).1 0 * φ ((tensorIndexEquiv j k).symm i).2 0

@[simp] theorem tensorState_apply {j k : ℕ} (ψ : QState j) (φ : QState k) (i : Fin (2^(j+k))) :
    tensorState ψ φ i 0 =
    ψ ((tensorIndexEquiv j k).symm i).1 0 * φ ((tensorIndexEquiv j k).symm i).2 0 := rfl

/-- Tensor product of basis states is the basis state at the combined index. -/
theorem ket_tensorState {j k : ℕ} (a : Fin (2^j)) (b : Fin (2^k)) :
    tensorState (ket a) (ket b) = ket (tensorIndexEquiv j k ⟨a, b⟩) := by
  funext i c
  fin_cases c
  show (if ((tensorIndexEquiv j k).symm i).1 = a then (1:ℂ) else 0) *
       (if ((tensorIndexEquiv j k).symm i).2 = b then 1 else 0) =
       if i = tensorIndexEquiv j k ⟨a, b⟩ then 1 else 0
  rcases eq_or_ne ((tensorIndexEquiv j k).symm i) ⟨a, b⟩ with h | h
  · have ha : ((tensorIndexEquiv j k).symm i).1 = a := congr_arg Prod.fst h
    have hb : ((tensorIndexEquiv j k).symm i).2 = b := congr_arg Prod.snd h
    have hi : i = tensorIndexEquiv j k ⟨a, b⟩ := (Equiv.symm_apply_eq _).mp h
    subst hi; simp
  · have hi : i ≠ tensorIndexEquiv j k ⟨a, b⟩ := fun heq => h (by simp [heq])
    simp only [if_neg hi]
    have hprod : ¬(((tensorIndexEquiv j k).symm i).1 = a ∧ ((tensorIndexEquiv j k).symm i).2 = b) :=
      fun ⟨h1, h2⟩ => h (Prod.ext h1 h2)
    rw [not_and] at hprod
    rcases eq_or_ne ((tensorIndexEquiv j k).symm i).1 a with h1 | h1
    · rw [if_pos h1, one_mul, if_neg (hprod h1)]
    · rw [if_neg h1, zero_mul]

-- ── Normalization of tensor products ─────────────────────────────────────────

private theorem tensorState_norm_sq {j k : ℕ} (ψ : QState j) (φ : QState k) :
    ∑ i : Fin (2^(j+k)), ‖tensorState ψ φ i 0‖^2 =
    (∑ a : Fin (2^j), ‖ψ a 0‖^2) * (∑ b : Fin (2^k), ‖φ b 0‖^2) := by
  simp_rw [tensorState_apply, norm_mul, mul_pow]
  rw [Fintype.sum_equiv (tensorIndexEquiv j k).symm _ (fun p => ‖ψ p.1 0‖^2 * ‖φ p.2 0‖^2)
      (fun _ => rfl)]
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Tensor product of normalized states is normalized. -/
theorem IsNormalized.tensorState {j k : ℕ} {ψ : QState j} {φ : QState k}
    (hψ : IsNormalized ψ) (hφ : IsNormalized φ) : IsNormalized (tensorState ψ φ) := by
  unfold IsNormalized
  rw [tensorState_norm_sq, hψ, hφ, mul_one]

end QLean

end
