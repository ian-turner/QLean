import QLean.Basic.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

open scoped Matrix Kronecker

noncomputable section

namespace QLean

-- ── Tensor index machinery ────────────────────────────────────────────────────

/-- Index equivalence for tensor products: `A` in the low `j` bits, `B` in the high `k` bits.
    LSB convention matches `finFunctionFinEquiv`: `(a, b) ↦ a.val + b.val * 2^j`. -/
def tensorIndexEquiv (j k : ℕ) : Fin (2^j) × Fin (2^k) ≃ Fin (2^(j+k)) :=
  (Equiv.prodComm _ _).trans
    (finProdFinEquiv.trans (finCongr (by rw [Nat.mul_comm, ← Nat.pow_add])))

lemma tensorIndexEquiv_symm_fst_val (j k : ℕ) (i : Fin (2^(j+k))) :
    ((tensorIndexEquiv j k).symm i).1.val = i.val % 2^j := by
  simp [tensorIndexEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, finCongr]

lemma tensorIndexEquiv_symm_snd_val (j k : ℕ) (i : Fin (2^(j+k))) :
    ((tensorIndexEquiv j k).symm i).2.val = i.val / 2^j := by
  simp [tensorIndexEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, finCongr]

-- ── Kronecker product machinery ───────────────────────────────────────────────

-- Any finCongr cast preserves the underlying ℕ value.
private lemma assoc_fst_val' (j k l : ℕ) (i : Fin (2^(j+(k+l)))) (i' : Fin (2^(j+k+l)))
    (hi : i'.val = i.val) :
    ((tensorIndexEquiv j k).symm ((tensorIndexEquiv (j+k) l).symm i').1).1.val =
    ((tensorIndexEquiv j (k+l)).symm i).1.val := by
  simp only [tensorIndexEquiv_symm_fst_val]
  rw [hi, Nat.pow_add (2:ℕ) j k, Nat.mod_mod_of_dvd _ ⟨2^k, rfl⟩]

private lemma assoc_mid_val' (j k l : ℕ) (i : Fin (2^(j+(k+l)))) (i' : Fin (2^(j+k+l)))
    (hi : i'.val = i.val) :
    ((tensorIndexEquiv j k).symm ((tensorIndexEquiv (j+k) l).symm i').1).2.val =
    ((tensorIndexEquiv k l).symm ((tensorIndexEquiv j (k+l)).symm i).2).1.val := by
  simp only [tensorIndexEquiv_symm_fst_val, tensorIndexEquiv_symm_snd_val]
  rw [hi, Nat.pow_add (2:ℕ) j k, Nat.mod_mul_right_div_self]

private lemma assoc_snd_val' (j k l : ℕ) (i : Fin (2^(j+(k+l)))) (i' : Fin (2^(j+k+l)))
    (hi : i'.val = i.val) :
    ((tensorIndexEquiv (j+k) l).symm i').2.val =
    ((tensorIndexEquiv k l).symm ((tensorIndexEquiv j (k+l)).symm i).2).2.val := by
  simp only [tensorIndexEquiv_symm_snd_val]
  rw [hi, Nat.pow_add (2:ℕ) j k, Nat.div_div_eq_div_mul]

/-- Reindexed Kronecker product: parallel composition of an `j`-qubit gate with a `k`-qubit gate,
    producing a `(j+k)`-qubit gate. Index `i : Fin (2^(j+k))` is split with `A` occupying
    the low `j` bits and `B` occupying the high `k` bits. -/
def kronQMatrix {j k : ℕ} (A : QMatrix j) (B : QMatrix k) : QMatrix (j + k) :=
  (A ⊗ₖ B).reindex (tensorIndexEquiv j k) (tensorIndexEquiv j k)

-- ── Key lemmas ────────────────────────────────────────────────────────────────

/-- Mixed-product property: `(A⊗B)(C⊗D) = (AC)⊗(BD)`. -/
theorem kronQMatrix_mul {j k : ℕ} (A C : QMatrix j) (B D : QMatrix k) :
    kronQMatrix (A * C) (B * D) = kronQMatrix A B * kronQMatrix C D := by
  unfold kronQMatrix
  rw [Matrix.mul_kronecker_mul]
  ext i p
  simp only [Matrix.mul_apply, Matrix.reindex_apply]
  apply Fintype.sum_equiv (tensorIndexEquiv j k)
  intro l
  simp [Equiv.symm_apply_apply]

/-- Adjoint distributes over `kronQMatrix`. -/
theorem kronQMatrix_conjTranspose {j k : ℕ} (A : QMatrix j) (B : QMatrix k) :
    (kronQMatrix A B)ᴴ = kronQMatrix Aᴴ Bᴴ := by
  simp [kronQMatrix, Matrix.conjTranspose_kronecker]

/-- Tensor product of identity matrices is the identity. -/
theorem kronQMatrix_one_one {j k : ℕ} :
    kronQMatrix (1 : QMatrix j) (1 : QMatrix k) = 1 := by
  unfold kronQMatrix
  rw [Matrix.one_kronecker_one]
  ext i p
  simp [Matrix.reindex_apply, Matrix.one_apply]

-- Associativity: the two ways to flatten three parallel gates agree.
-- The reindex by finCongr (2^·) (add_assoc) bridges the type-level
-- j+k+l = j+(k+l) isomorphism.  The proof reduces to three Nat arithmetic
-- identities about % and / with powers of 2.
theorem kronQMatrix_assoc {j k l : ℕ} (A : QMatrix j) (B : QMatrix k) (C : QMatrix l) :
    (kronQMatrix (kronQMatrix A B) C).reindex
        (finCongr (congr_arg (2 ^ ·) (Nat.add_assoc j k l)))
        (finCongr (congr_arg (2 ^ ·) (Nat.add_assoc j k l))) =
    kronQMatrix A (kronQMatrix B C) := by
  ext i p
  simp only [kronQMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
             Matrix.kroneckerMap_apply]
  have hiv : ((finCongr (congr_arg (2^·) (Nat.add_assoc j k l))).symm i).val = i.val := by
    simp [finCongr]
  have hpv : ((finCongr (congr_arg (2^·) (Nat.add_assoc j k l))).symm p).val = p.val := by
    simp [finCongr]
  rw [Fin.ext (assoc_fst_val' j k l i _ hiv), Fin.ext (assoc_fst_val' j k l p _ hpv),
      Fin.ext (assoc_mid_val' j k l i _ hiv), Fin.ext (assoc_mid_val' j k l p _ hpv),
      Fin.ext (assoc_snd_val' j k l i _ hiv), Fin.ext (assoc_snd_val' j k l p _ hpv),
      mul_assoc]

end QLean

end
