import QLean.Circuit.Type
import QLean.Basic.Tensor
import QLean.Basic.Hilbert

namespace QLean

open Circuit

noncomputable section

-- ── Denotational semantics ────────────────────────────────────────────────────

namespace Circuit

/-- Map a circuit to the unitary it denotes. `seq` applies left-to-right, so
    `c₁` acts first and `eval (seq c₁ c₂) = eval c₂ * eval c₁`. -/
def eval : Circuit n → QMatrix n
  | .id        => 1
  | .gate U    => U
  | .seq c₁ c₂ => eval c₂ * eval c₁
  | .par c₁ c₂ => kron (eval c₁) (eval c₂)

@[simp] theorem eval_id  : eval (1 : Circuit n) = 1 := rfl
@[simp] theorem eval_gate (U : QMatrix n) : eval (.gate U) = U := rfl
@[simp] theorem eval_seq (c₁ c₂ : Circuit n) : eval (c₁ * c₂) = eval c₂ * eval c₁ := rfl
@[simp] theorem eval_par {j k : ℕ} (c₁ : Circuit j) (c₂ : Circuit k) :
    eval (c₁ ⊗ c₂) = kron (eval c₁) (eval c₂) := rfl

/-- `eval_castN`: transporting across a qubit-count equality is a `reindex` at matrix level. -/
@[simp] theorem eval_castN (h : m = n) (c : Circuit m) :
    eval (castN h c) =
    (eval c).reindex (finCongr (congr_arg (2^·) h)) (finCongr (congr_arg (2^·) h)) := by
  cases h; simp [castN]

end Circuit

-- ── Well-formedness ───────────────────────────────────────────────────────────

/-- A circuit is well-formed if every gate is unitary. Defined as a `def` to avoid
    dependent elimination issues with the `par` index. -/
def Circuit.WF : Circuit n → Prop
  | Circuit.id        => True
  | Circuit.gate U    => IsUnitary U
  | Circuit.seq c₁ c₂ => Circuit.WF c₁ ∧ Circuit.WF c₂
  | Circuit.par c₁ c₂ => Circuit.WF c₁ ∧ Circuit.WF c₂

@[simp] theorem wf_id   : Circuit.WF (1 : Circuit n) := trivial
@[simp] theorem wf_gate {U : QMatrix n} : Circuit.WF (.gate U) ↔ IsUnitary U := Iff.rfl
@[simp] theorem wf_seq  {c₁ c₂ : Circuit n} :
    Circuit.WF (c₁ * c₂) ↔ Circuit.WF c₁ ∧ Circuit.WF c₂ := Iff.rfl
@[simp] theorem wf_par  {c₁ : Circuit j} {c₂ : Circuit k} :
    Circuit.WF (c₁ ⊗ c₂) ↔ Circuit.WF c₁ ∧ Circuit.WF c₂ := Iff.rfl

-- ── WF implies unitarity ──────────────────────────────────────────────────────

/-- A well-formed circuit evaluates to a unitary matrix. -/
theorem Circuit.eval_unitary (c : Circuit n) (h : c.WF) : IsUnitary (eval c) := by
  induction c with
  | id => unfold eval IsUnitary; simp [Matrix.conjTranspose_one]
  | gate U => exact h
  | seq c₁ c₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact IsUnitary.mul (ih₂ h₂) (ih₁ h₁)
  | par c₁ c₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact IsUnitary.kron (ih₁ h₁) (ih₂ h₂)

-- ── State transformation and preparation ──────────────────────────────────────

/-- `C.maps φ ψ` holds when circuit `C` sends input state `φ` to output state `ψ`. -/
def Circuit.maps (C : Circuit n) (φ ψ : QVector n) : Prop :=
  eval C * φ = ψ

@[simp] theorem Circuit.maps_iff (C : Circuit n) (φ ψ : QVector n) :
    C.maps φ ψ ↔ eval C * φ = ψ := Iff.rfl

/-- `C.prepares ψ` holds when `C` produces state `ψ` from the all-zeros input `|0…0⟩`. -/
abbrev Circuit.prepares (C : Circuit n) (ψ : QVector n) : Prop :=
  C.maps (ket 0) ψ

theorem Circuit.maps_id (φ : QVector n) : (1 : Circuit n).maps φ φ := by
  simp [Circuit.maps]

/-- If `C₁` maps `φ` to `χ` and `C₂` maps `χ` to `ψ`, then `C₁ * C₂` maps `φ` to `ψ`. -/
theorem Circuit.maps_comp {C₁ C₂ : Circuit n} {φ χ ψ : QVector n}
    (h₁ : C₁.maps φ χ) (h₂ : C₂.maps χ ψ) : (C₁ * C₂).maps φ ψ := by
  simp only [Circuit.maps_iff] at *
  rw [eval_seq, Matrix.mul_assoc, h₁, h₂]

end

end QLean
