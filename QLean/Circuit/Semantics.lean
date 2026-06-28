import QLean.Circuit.Type
import QLean.Basic.Tensor
import QLean.Basic.Embed

namespace QLean

open QCircuit

noncomputable section

-- ── Denotational semantics ────────────────────────────────────────────────────

namespace QCircuit

/-- Map a circuit to the unitary it denotes. `seq` is a homomorphism onto matrix
    multiplication: `eval (seq c₁ c₂) = eval c₁ * eval c₂`, so the rightmost
    factor `c₂` acts first. -/
def eval : QCircuit n → QMatrix n
  | .id        => 1
  | .gate U    => U
  | .seq c₁ c₂ => eval c₁ * eval c₂
  | .par c₁ c₂ => kron (eval c₁) (eval c₂)
  | .embed qs c => QLean.embed qs (eval c)

@[simp] theorem eval_id  : eval (1 : QCircuit n) = 1 := rfl
@[simp] theorem eval_gate (U : QMatrix n) : eval (.gate U) = U := rfl
@[simp] theorem eval_seq (c₁ c₂ : QCircuit n) : eval (c₁ * c₂) = eval c₁ * eval c₂ := rfl
@[simp] theorem eval_par {j k : ℕ} (c₁ : QCircuit j) (c₂ : QCircuit k) :
    eval (c₁ ⊗ c₂) = kron (eval c₁) (eval c₂) := rfl
@[simp] theorem eval_embed {k : ℕ} (qs : Fin k ↪ Fin n) (c : QCircuit k) :
    eval (.embed qs c) = QLean.embed qs (eval c) := rfl

/-- Transporting a circuit across a qubit-count equality is a `reindex` at the matrix level. -/
@[simp] theorem eval_castN (h : m = n) (c : QCircuit m) :
    eval (castN h c) =
    (eval c).reindex (finCongr (congr_arg (2^·) h)) (finCongr (congr_arg (2^·) h)) := by
  cases h; simp [castN]

end QCircuit

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- A circuit is well-formed if every gate is unitary. Defined as a `def` to avoid
    dependent elimination issues with the `par` index. -/
def QCircuit.WF : QCircuit n → Prop
  | QCircuit.id        => True
  | QCircuit.gate U    => IsUnitary U
  | QCircuit.seq c₁ c₂ => QCircuit.WF c₁ ∧ QCircuit.WF c₂
  | QCircuit.par c₁ c₂ => QCircuit.WF c₁ ∧ QCircuit.WF c₂
  | QCircuit.embed _ c => QCircuit.WF c

@[simp] theorem wf_id   : QCircuit.WF (1 : QCircuit n) := trivial
@[simp] theorem wf_gate {U : QMatrix n} : QCircuit.WF (.gate U) ↔ IsUnitary U := Iff.rfl
@[simp] theorem wf_seq  {c₁ c₂ : QCircuit n} :
    QCircuit.WF (c₁ * c₂) ↔ QCircuit.WF c₁ ∧ QCircuit.WF c₂ := Iff.rfl
@[simp] theorem wf_par  {c₁ : QCircuit j} {c₂ : QCircuit k} :
    QCircuit.WF (c₁ ⊗ c₂) ↔ QCircuit.WF c₁ ∧ QCircuit.WF c₂ := Iff.rfl
@[simp] theorem wf_embed {k : ℕ} {qs : Fin k ↪ Fin n} {c : QCircuit k} :
    QCircuit.WF (.embed qs c) ↔ QCircuit.WF c := Iff.rfl

-- ── WF implies unitarity ──────────────────────────────────────────────────────

/-- A well-formed circuit evaluates to a unitary matrix. -/
theorem QCircuit.eval_unitary (c : QCircuit n) (h : c.WF) : IsUnitary (eval c) := by
  induction c with
  | id => unfold eval IsUnitary; simp [Matrix.conjTranspose_one]
  | gate U => exact h
  | seq c₁ c₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact IsUnitary.mul (ih₁ h₁) (ih₂ h₂)
  | par c₁ c₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact IsUnitary.kron (ih₁ h₁) (ih₂ h₂)
  | embed qs c ih => exact embed_unitary qs (ih h)

end

end QLean
