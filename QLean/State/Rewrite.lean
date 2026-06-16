import QLean.State.Semantics
import QLean.Circuit.Rewrite

open scoped QLean.Notation

namespace QLean

noncomputable section

-- ── QState.Equiv ──────────────────────────────────────────────────────────────

/-- Two state expressions are equivalent if they denote the same vector. -/
def QState.Equiv (s t : QState n) : Prop := QState.eval s = QState.eval t

@[reducible] instance : HasEquiv (QState n) := ⟨QState.Equiv⟩

@[refl]  theorem QState.Equiv.refl  (s : QState n) : s ≈ s := rfl
@[symm]  theorem QState.Equiv.symm  {s t : QState n} : s ≈ t → t ≈ s := Eq.symm
@[trans] theorem QState.Equiv.trans {s t u : QState n} : s ≈ t → t ≈ u → s ≈ u := Eq.trans

instance : Trans (@QState.Equiv n) (@QState.Equiv n) (@QState.Equiv n) :=
  ⟨QState.Equiv.trans⟩

-- ── Congruence lemmas ─────────────────────────────────────────────────────────

theorem QState.Equiv.apply_congr {C : Circuit n} {s t : QState n}
    (h : s ≈ t) : C * s ≈ C * t := by
  simp only [QState.Equiv, QState.eval_apply]; rw [h]

theorem Circuit.mapsExpr_iff {C : Circuit n} {s t : QState n} :
    C.mapsExpr s t ↔ C * s ≈ t := Iff.rfl

theorem QState.Equiv.add_congr {s s' t t' : QState n}
    (hs : s ≈ s') (ht : t ≈ t') : s + t ≈ s' + t' := by
  simp only [QState.Equiv, QState.eval_add]; rw [hs, ht]

theorem QState.Equiv.smul_congr {s s' : QState n} (α : ℂ)
    (hs : s ≈ s') : α • s ≈ α • s' := by
  simp only [QState.Equiv, QState.eval_smul]; rw [hs]

theorem QState.Equiv.tensor_congr {s s' : QState j} {t t' : QState k}
    (hs : s ≈ s') (ht : t ≈ t') : s ⊗ₛ t ≈ s' ⊗ₛ t' := by
  simp only [QState.Equiv, QState.eval_tensor]; rw [hs, ht]

-- ── Distributivity rules ──────────────────────────────────────────────────────

theorem QState.add_tensor_left (s t : QState j) (u : QState k) :
    (s + t) ⊗ₛ u ≈ s ⊗ₛ u + t ⊗ₛ u := by
  simp only [QState.Equiv, QState.eval_tensor, QState.eval_add]
  funext i c; fin_cases c
  simp [tensorState_apply, Matrix.add_apply, add_mul]

theorem QState.tensor_add_right (s : QState j) (t u : QState k) :
    s ⊗ₛ (t + u) ≈ s ⊗ₛ t + s ⊗ₛ u := by
  simp only [QState.Equiv, QState.eval_tensor, QState.eval_add]
  funext i c; fin_cases c
  simp [tensorState_apply, Matrix.add_apply, mul_add]

theorem QState.smul_tensor_left (α : ℂ) (s : QState j) (t : QState k) :
    (α • s) ⊗ₛ t ≈ α • (s ⊗ₛ t) := by
  simp only [QState.Equiv, QState.eval_tensor, QState.eval_smul, tensorState_smul_left]

theorem QState.tensor_smul_right (α : ℂ) (s : QState j) (t : QState k) :
    s ⊗ₛ (α • t) ≈ α • (s ⊗ₛ t) := by
  simp only [QState.Equiv, QState.eval_tensor, QState.eval_smul]
  funext r c
  simp only [tensorState, Matrix.smul_apply, smul_eq_mul]
  ring

-- ── Circuit.Equiv via symbolic states ─────────────────────────────────────────

/-- Equivalent circuits act identically on every symbolic state expression. -/
theorem Circuit.Equiv.apply_state {n : ℕ} {c₁ c₂ : Circuit n}
    (h : c₁ ≈ c₂) (s : QState n) : c₁ * s ≈ c₂ * s := by
  simp only [QState.Equiv, QState.eval_apply]; rw [h]

/-- Two circuits are equivalent iff they act identically on every symbolic basis ket. -/
theorem Circuit.Equiv.basis_iff_state {n : ℕ} (c₁ c₂ : Circuit n) :
    c₁ ≈ c₂ ↔ ∀ i : Fin (2^n), c₁ * |i⟩ ≈ c₂ * |i⟩ := by
  rw [Circuit.Equiv.basis_iff]
  simp [QState.Equiv, QState.eval_apply, QState.eval_basis]

/-- Two circuits are equivalent iff they act identically on every symbolic state expression.
    The basis-indexed form is usually more convenient; this stronger form avoids index-chasing
    when the input state is already in symbolic normal form. -/
theorem Circuit.Equiv.equiv_iff_all_states {n : ℕ} (c₁ c₂ : Circuit n) :
    c₁ ≈ c₂ ↔ ∀ s : QState n, c₁ * s ≈ c₂ * s :=
  ⟨fun h s => h.apply_state s,
   fun h => (basis_iff_state c₁ c₂).mpr (fun i => h |i⟩)⟩

end  -- noncomputable

end QLean
