import QLean.State.Semantics
import QLean.Circuit.Rewrite

open scoped QLean.Notation

namespace QLean

noncomputable section

-- ── QState.Equiv ──────────────────────────────────────────────────────────────

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

-- ── Circuit action on symbolic states ────────────────────────────────────────

/-- A circuit distributes over state addition. -/
theorem Circuit.apply_add (C : Circuit n) (s t : QState n) :
    C * (s + t) ≈ C * s + C * t := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_add, Matrix.mul_add]

/-- A circuit commutes with scalar multiplication. -/
theorem Circuit.apply_smul (C : Circuit n) (α : ℂ) (s : QState n) :
    C * (α • s) ≈ α • (C * s) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_smul, Matrix.mul_smul]

/-- Sequential circuit composition associates with state application:
    applying `c₁ * c₂` (first c₁, then c₂) to s equals first applying c₁ to s,
    then applying c₂ to the result. -/
theorem Circuit.seq_action (c₁ c₂ : Circuit n) (s : QState n) :
    (c₁ * c₂) * s ≈ c₂ * (c₁ * s) := by
  simp only [QState.Equiv, QState.eval_apply, eval_seq, Matrix.mul_assoc]

/-- The identity circuit acts trivially. -/
theorem Circuit.id_action (s : QState n) : (1 : Circuit n) * s ≈ s := by
  simp only [QState.Equiv, QState.eval_apply, eval_id, Matrix.one_mul]

/-- Parallel circuits act componentwise on tensor-product states. -/
theorem Circuit.par_action_tensor (c₁ : Circuit j) (c₂ : Circuit k)
    (s : QState j) (t : QState k) :
    (c₁ ⊗ c₂) * (s ⊗ₛ t) ≈ (c₁ * s) ⊗ₛ (c₂ * t) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_tensor, eval_par, kron_tensorState]

/-- Tensor product of state expressions is associative (right-unit case).
    Both sides have type `QState (j + k + 1)` since `(j+k)+1 = j+(k+1)` definitionally. -/
theorem QState.tensor_assoc {j k : ℕ} (s : QState j) (t : QState k) (u : QState 1) :
    (s ⊗ₛ t) ⊗ₛ u ≈ (s ⊗ₛ (t ⊗ₛ u : QState (k + 1)) : QState (j + (k + 1))) := by
  simp only [QState.Equiv, QState.eval_tensor, tensorState_assoc_one]

/-- The all-zero basis ket splits as a tensor of all-zero kets. -/
theorem QState.ket_zero_tensor (j k : ℕ) :
    (⎸0⟩ : QState (j + k)) ≈ (⎸0⟩ : QState j) ⊗ₛ (⎸0⟩ : QState k) := by
  simp only [QState.Equiv, QState.eval_basis, QState.eval_tensor, ket_tensorState]
  congr 1

-- ── Circuit.Equiv via symbolic states ─────────────────────────────────────────

/-- Equivalent circuits act identically on every symbolic state expression. -/
theorem Circuit.Equiv.apply_state {n : ℕ} {c₁ c₂ : Circuit n}
    (h : c₁ ≈ c₂) (s : QState n) : c₁ * s ≈ c₂ * s := by
  simp only [QState.Equiv, QState.eval_apply]; rw [h]

end  -- noncomputable

end QLean
