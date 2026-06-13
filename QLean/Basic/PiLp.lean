import QLean.Basic.Matrix

open scoped Matrix

noncomputable section

namespace QLean

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

end QLean

end
