import QLean.State.Semantics

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
  unfold QState.Equiv
  simp only [QState.eval_tensor, QState.eval_smul, tensorState_smul_left]

theorem QState.tensor_smul_right (α : ℂ) (s : QState j) (t : QState k) :
    s ⊗ₛ (α • t) ≈ α • (s ⊗ₛ t) := by
  unfold QState.Equiv
  simp only [QState.eval_tensor, QState.eval_smul]
  funext i c; fin_cases c
  simp only [tensorState_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end  -- noncomputable

end QLean
