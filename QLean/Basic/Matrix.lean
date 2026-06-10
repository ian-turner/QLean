import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic

open scoped Matrix

namespace QLean

abbrev QMatrix (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

def IsUnitary {n : ℕ} (U : QMatrix n) : Prop := U * Uᴴ = 1

namespace IsUnitary

theorem conj_mul {n : ℕ} {U : QMatrix n} (h : IsUnitary U) : Uᴴ * U = 1 :=
  mul_eq_one_comm.mp h

theorem mul {n : ℕ} {U V : QMatrix n} (hu : IsUnitary U) (hv : IsUnitary V) :
    IsUnitary (U * V) := by
  unfold IsUnitary
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
      Matrix.mul_assoc U, hv, Matrix.mul_one, hu]

end IsUnitary

end QLean
