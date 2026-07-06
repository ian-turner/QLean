import QLean.Basic.Tensor
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Matrix

noncomputable section

namespace QLean

-- ── QVector ───────────────────────────────────────────────────────────────────

/-- `n`-qubit quantum state: a column vector in `ℂ^(2^n)`. A gate acts on a state by
    plain matrix multiplication `U * ψ`. -/
abbrev QVector (n : ℕ) := Matrix (Fin (2^n)) (Fin 1) ℂ

-- ── Normalization predicate ───────────────────────────────────────────────────

/-- A quantum state is normalized if the squared norms of its amplitudes sum to 1. -/
def IsNormalized {n : ℕ} (ψ : QVector n) : Prop := ∑ i, ‖ψ i 0‖^2 = 1

-- ── Computational basis ───────────────────────────────────────────────────────

/-- The `i`-th computational basis state: amplitude 1 at row `i`, 0 elsewhere. -/
def ket {n : ℕ} (i : Fin (2^n)) : QVector n := fun j _ => if j = i then 1 else 0

@[simp] theorem ket_apply {n : ℕ} (i j : Fin (2^n)) :
    ket i j 0 = if j = i then 1 else 0 := rfl

theorem ket_normalized {n : ℕ} (i : Fin (2^n)) : IsNormalized (ket i) := by
  unfold IsNormalized
  have key : ∀ j : Fin (2^n), ‖ket i j 0‖^2 = if j = i then 1 else 0 := by
    intro j; simp only [ket_apply]; split_ifs <;> simp
  simp_rw [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `(M * ket i) r 0 = M r i`: multiplying by a basis ket reads off a single column. -/
theorem mul_ket_apply {n : ℕ} (M : QMatrix n) (i r : Fin (2 ^ n)) :
    (M * ket i) r 0 = M r i := by
  simp [Matrix.mul_apply, ket_apply, mul_ite, Finset.sum_ite_eq', Finset.mem_univ]

/-- The all-ones computational basis index on `n` qubits: `2^n - 1`, the top index of
    `Fin (2^n)`. `ket (allOnes n)` is the all-ones ket `|1…1⟩`. -/
def allOnes (n : ℕ) : Fin (2^n) :=
  ⟨2^n - 1, by have : 0 < 2^n := pow_pos (by norm_num) n; omega⟩

@[simp] theorem allOnes_val (n : ℕ) : (allOnes n).val = 2^n - 1 := rfl

-- ── Tensor product of states ──────────────────────────────────────────────────

/-- Tensor product of a `j`-qubit state and a `k`-qubit state.
    Index `i : Fin (2^(j+k))` decomposes via `tensorIndexEquiv` as `(low j bits, high k bits)`. -/
def tensorState {j k : ℕ} (ψ : QVector j) (φ : QVector k) : QVector (j+k) :=
  fun i _ => ψ ((tensorIndexEquiv j k).symm i).1 0 * φ ((tensorIndexEquiv j k).symm i).2 0

@[simp] theorem tensorState_apply {j k : ℕ} (ψ : QVector j) (φ : QVector k) (i : Fin (2^(j+k))) :
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

theorem tensorState_smul_left {j k : ℕ} (c : ℂ) (ψ : QVector j) (φ : QVector k) :
    tensorState (c • ψ) φ = c • tensorState ψ φ := by
  funext r s
  simp only [tensorState, Matrix.smul_apply, smul_eq_mul]
  ring

theorem tensorState_smul_right {j k : ℕ} (c : ℂ) (ψ : QVector j) (φ : QVector k) :
    tensorState ψ (c • φ) = c • tensorState ψ φ := by
  funext r s
  simp only [tensorState, Matrix.smul_apply, smul_eq_mul]
  ring

theorem tensorState_add_left {j k : ℕ} (ψ χ : QVector j) (φ : QVector k) :
    tensorState (ψ + χ) φ = tensorState ψ φ + tensorState χ φ := by
  funext r s
  simp only [tensorState, Matrix.add_apply]
  ring

theorem tensorState_add_right {j k : ℕ} (ψ : QVector j) (φ χ : QVector k) :
    tensorState ψ (φ + χ) = tensorState ψ φ + tensorState ψ χ := by
  funext r s
  simp only [tensorState, Matrix.add_apply]
  ring

-- ── Kronecker product on states ───────────────────────────────────────────────

/-- `(A⊗B)(ψ⊗φ) = (Aψ)⊗(Bφ)`: the Kronecker product of gates acts componentwise on product states. -/
theorem kron_tensorState {j k : ℕ} (A : QMatrix j) (B : QMatrix k)
    (ψ : QVector j) (φ : QVector k) :
    kron A B * tensorState ψ φ = tensorState (A * ψ) (B * φ) := by
  funext r s
  obtain rfl : s = 0 := Subsingleton.elim s 0
  simp only [Matrix.mul_apply, tensorState_apply, kron, Matrix.reindex_apply,
             Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  -- Change sum variable: Fin (2^(j+k)) → Fin (2^j) × Fin (2^k)
  rw [Fintype.sum_equiv (tensorIndexEquiv j k).symm
      (fun x => A ((tensorIndexEquiv j k).symm r).1 ((tensorIndexEquiv j k).symm x).1 *
                B ((tensorIndexEquiv j k).symm r).2 ((tensorIndexEquiv j k).symm x).2 *
                (ψ ((tensorIndexEquiv j k).symm x).1 0 *
                 φ ((tensorIndexEquiv j k).symm x).2 0))
      (fun p => A ((tensorIndexEquiv j k).symm r).1 p.1 *
                B ((tensorIndexEquiv j k).symm r).2 p.2 * (ψ p.1 0 * φ p.2 0))
      (fun _ => rfl)]
  -- Factor ∑_(a,b) fa·ga·(fb·gb) into (∑_a fa·ga)·(∑_b fb·gb); `mul_mul_mul_comm` separates the factors.
  simp_rw [Fintype.sum_prod_type, mul_mul_mul_comm, ← Finset.mul_sum, ← Finset.sum_mul]

-- ── Tensor product associativity (right-unit case) ───────────────────────────

/-- Tensor product of states is associative when the third factor is a 1-qubit state.
    Types agree because `(j+k)+1 = j+(k+1)` definitionally. -/
theorem tensorState_assoc_one {j k : ℕ} (ψ : QVector j) (φ : QVector k) (χ : QVector 1) :
    tensorState (tensorState ψ φ) χ = tensorState ψ (tensorState φ χ) := by
  funext i c; obtain rfl : c = 0 := Subsingleton.elim c 0
  simp only [tensorState_apply]
  have hfst : ((tensorIndexEquiv j k).symm ((tensorIndexEquiv (j + k) 1).symm i).1).1 =
              ((tensorIndexEquiv j (k + 1)).symm i).1 := by
    apply Fin.ext
    simp only [tensorIndexEquiv_symm_fst_val]
    rw [pow_add (2 : ℕ) j k, Nat.mod_mod_of_dvd _ ⟨2 ^ k, rfl⟩]
  have hmid : ((tensorIndexEquiv j k).symm ((tensorIndexEquiv (j + k) 1).symm i).1).2 =
              ((tensorIndexEquiv k 1).symm ((tensorIndexEquiv j (k + 1)).symm i).2).1 := by
    apply Fin.ext
    simp only [tensorIndexEquiv_symm_fst_val, tensorIndexEquiv_symm_snd_val]
    rw [pow_add (2 : ℕ) j k, Nat.mod_mul_right_div_self]
  have hsnd : ((tensorIndexEquiv (j + k) 1).symm i).2 =
              ((tensorIndexEquiv k 1).symm ((tensorIndexEquiv j (k + 1)).symm i).2).2 := by
    apply Fin.ext
    simp only [tensorIndexEquiv_symm_snd_val]
    rw [pow_add (2 : ℕ) j k, ← Nat.div_div_eq_div_mul]
  rw [hfst, hmid, hsnd, mul_assoc]

-- ── Normalization of tensor products ─────────────────────────────────────────

private theorem tensorState_norm_sq {j k : ℕ} (ψ : QVector j) (φ : QVector k) :
    ∑ i : Fin (2^(j+k)), ‖tensorState ψ φ i 0‖^2 =
    (∑ a : Fin (2^j), ‖ψ a 0‖^2) * (∑ b : Fin (2^k), ‖φ b 0‖^2) := by
  simp_rw [tensorState_apply, norm_mul, mul_pow]
  rw [Fintype.sum_equiv (tensorIndexEquiv j k).symm _ (fun p => ‖ψ p.1 0‖^2 * ‖φ p.2 0‖^2)
      (fun _ => rfl)]
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Tensor product of normalized states is normalized. -/
theorem IsNormalized.tensorState {j k : ℕ} {ψ : QVector j} {φ : QVector k}
    (hψ : IsNormalized ψ) (hφ : IsNormalized φ) : IsNormalized (tensorState ψ φ) := by
  unfold IsNormalized
  rw [tensorState_norm_sq, hψ, hφ, mul_one]

end QLean

end

