import QLean.State.Type
import QLean.Basic.Hilbert
import QLean.Circuit.Semantics

namespace QLean

namespace QState

noncomputable section

-- ── Denotational semantics ────────────────────────────────────────────────────

/-- Map a symbolic state expression to the column vector it denotes. -/
def eval : QState n → QVector n
  | .basis i    => ket i
  | .smul α s   => α • eval s
  | .add s t    => eval s + eval t
  | .tensor s t => tensorState (eval s) (eval t)
  | .apply C s  => Circuit.eval C * eval s

@[simp] theorem eval_basis (i : Fin (2^n)) : eval (.basis i) = ket i := rfl
@[simp] theorem eval_smul (α : ℂ) (s : QState n) : eval (α • s) = α • eval s := rfl
@[simp] theorem eval_add (s t : QState n) : eval (s + t) = eval s + eval t := rfl
@[simp] theorem eval_tensor {j k : ℕ} (s : QState j) (t : QState k) :
    eval (s ⊗ₛ t) = tensorState (eval s) (eval t) := rfl
@[simp] theorem eval_apply (C : Circuit n) (s : QState n) :
    eval (C * s) = Circuit.eval C * eval s := rfl

theorem eval_castN (h : m = n) (s : QState m) : eval (castN h s) = h ▸ eval s := by
  cases h; rfl

-- ── Normalization ─────────────────────────────────────────────────────────────

/-- A state expression is normalized when its denotation is a unit vector. -/
def IsNormalized (s : QState n) : Prop := QLean.IsNormalized (eval s)

theorem IsNormalized.tensor {j k : ℕ} {s : QState j} {t : QState k}
    (hs : s.IsNormalized) (ht : t.IsNormalized) : (s ⊗ₛ t).IsNormalized := by
  unfold IsNormalized; simp only [eval_tensor]
  exact QLean.IsNormalized.tensorState hs ht

end  -- noncomputable

end QState

-- ── Circuit–QState bridge ─────────────────────────────────────────────────────

open Circuit

noncomputable section

/-- `C.mapsExpr s t` holds when `C` maps the denotation of `s` to the denotation of `t`. -/
def Circuit.mapsExpr (C : Circuit n) (s t : QState n) : Prop :=
  C.maps (QState.eval s) (QState.eval t)

/-- A parallel circuit maps a tensor-product state expression componentwise. -/
theorem Circuit.maps_tensor {j k : ℕ} {c₁ : Circuit j} {c₂ : Circuit k}
    {s s' : QState j} {t t' : QState k}
    (h₁ : c₁.mapsExpr s s') (h₂ : c₂.mapsExpr t t') :
    (c₁ ⊗ c₂).mapsExpr (s ⊗ₛ t) (s' ⊗ₛ t') := by
  unfold Circuit.mapsExpr Circuit.maps at *
  simp only [QState.eval_tensor, eval_par]
  rw [kron_tensorState, h₁, h₂]

end  -- noncomputable

end QLean
