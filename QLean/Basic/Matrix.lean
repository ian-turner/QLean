import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic

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

end QLean
