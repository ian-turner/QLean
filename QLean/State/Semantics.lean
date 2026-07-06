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
  | .apply C s  => QCircuit.eval C * eval s

@[simp] theorem eval_basis (i : Fin (2^n)) : eval (.basis i) = ket i := rfl
@[simp] theorem eval_smul (α : ℂ) (s : QState n) : eval (α • s) = α • eval s := rfl
@[simp] theorem eval_add (s t : QState n) : eval (s + t) = eval s + eval t := rfl
@[simp] theorem eval_tensor {j k : ℕ} (s : QState j) (t : QState k) :
    eval (s ⊗ t) = tensorState (eval s) (eval t) := rfl
@[simp] theorem eval_apply (C : QCircuit n) (s : QState n) :
    eval (C * s) = QCircuit.eval C * eval s := rfl

-- ── Normalization ─────────────────────────────────────────────────────────────

/-- A state expression is normalized when its denotation is a unit vector. -/
def IsNormalized (s : QState n) : Prop := QLean.IsNormalized (eval s)

theorem IsNormalized.tensor {j k : ℕ} {s : QState j} {t : QState k}
    (hs : s.IsNormalized) (ht : t.IsNormalized) : (s ⊗ t).IsNormalized := by
  unfold IsNormalized; simp only [eval_tensor]
  exact QLean.IsNormalized.tensorState hs ht

end  -- noncomputable

end QState

end QLean
