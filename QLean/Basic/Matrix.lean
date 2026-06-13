import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic

open scoped Matrix

namespace QLean

/-- `n`-qubit gate type: complex 2^n × 2^n matrices. -/
abbrev QMatrix (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-- `U` is unitary: `U * Uᴴ = 1`. The other direction is `conj_mul`. -/
def IsUnitary {n : ℕ} (U : QMatrix n) : Prop := U * Uᴴ = 1

namespace IsUnitary

/-- The adjoint direction: `Uᴴ * U = 1`. -/
theorem conj_mul {n : ℕ} {U : QMatrix n} (h : IsUnitary U) : Uᴴ * U = 1 :=
  mul_eq_one_comm.mp h

/-- Composition of unitaries is unitary. -/
theorem mul {n : ℕ} {U V : QMatrix n} (hu : IsUnitary U) (hv : IsUnitary V) :
    IsUnitary (U * V) := by
  unfold IsUnitary
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
      Matrix.mul_assoc U, hv, Matrix.mul_one, hu]

end IsUnitary

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

end QLean
