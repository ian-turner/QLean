import QLean.Basic.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix InnerProductSpace

noncomputable section

namespace QLean

/-- `n`-qubit quantum state: a vector in `ℂ^(2^n)` with inner product structure. -/
abbrev QState (n : ℕ) := EuclideanSpace ℂ (Fin (2^n))

namespace QState

/-- Coerce a `QState` to a plain function (for `Matrix.mulVec` bridge). All `WithLp`
    coercions in the library are funnelled through this pair. -/
def toFun {n : ℕ} (ψ : QState n) : Fin (2^n) → ℂ :=
  WithLp.equiv 2 _ ψ

/-- Lift a plain function to a `QState`. -/
def ofFun {n : ℕ} (f : Fin (2^n) → ℂ) : QState n :=
  (WithLp.equiv 2 _).symm f

@[simp] lemma toFun_ofFun {n : ℕ} (f : Fin (2^n) → ℂ) :
    (ofFun f).toFun = f := by simp [toFun, ofFun]

@[simp] lemma ofFun_toFun {n : ℕ} (ψ : QState n) :
    ofFun ψ.toFun = ψ := by simp [toFun, ofFun]

/-- Bridge: our `toFun` equals Mathlib's `.ofLp` field (the underlying function of a `WithLp`). -/
@[simp] lemma toFun_apply_eq_ofLp {n : ℕ} (ψ : QState n) (i : Fin (2^n)) :
    ψ.toFun i = ψ.ofLp i := rfl

end QState

namespace QMatrix

/-- Act on a quantum state: `U.act ψ = U · ψ` (matrix-vector product). -/
def act {n : ℕ} (U : QMatrix n) (ψ : QState n) : QState n :=
  QState.ofFun (U.mulVec ψ.toFun)

@[simp] theorem act_toFun {n : ℕ} (U : QMatrix n) (ψ : QState n) :
    (U.act ψ).toFun = U.mulVec ψ.toFun := by simp [act, QState.toFun, QState.ofFun]

theorem act_mul {n : ℕ} (U V : QMatrix n) (ψ : QState n) :
    QMatrix.act (U * V) ψ = U.act (V.act ψ) := by
  simp [act, QState.toFun, QState.ofFun, Matrix.mulVec_mulVec]

theorem act_one {n : ℕ} (ψ : QState n) : QMatrix.act (1 : QMatrix n) ψ = ψ := by
  simp [act, QState.toFun, QState.ofFun]

end QMatrix

end QLean

end
