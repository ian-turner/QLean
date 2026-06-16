import QLean.State.Semantics
import QLean.Circuit.Rewrite
import Mathlib.Tactic.GCongr

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

@[gcongr]
theorem QState.Equiv.apply_congr {C : Circuit n} {s t : QState n}
    (h : s ≈ t) : C * s ≈ C * t := by
  simp only [QState.Equiv, QState.eval_apply]; rw [h]

@[gcongr]
theorem QState.Equiv.add_congr {s s' t t' : QState n}
    (hs : s ≈ s') (ht : t ≈ t') : s + t ≈ s' + t' := by
  simp only [QState.Equiv, QState.eval_add]; rw [hs, ht]

@[gcongr]
theorem QState.Equiv.smul_congr {s s' : QState n} (α : ℂ)
    (hs : s ≈ s') : α • s ≈ α • s' := by
  simp only [QState.Equiv, QState.eval_smul]; rw [hs]

@[gcongr]
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
    (❘0⟩ : QState (j + k)) ≈ (❘0⟩ : QState j) ⊗ₛ (❘0⟩ : QState k) := by
  simp only [QState.Equiv, QState.eval_basis, QState.eval_tensor, ket_tensorState]
  congr 1

/-- A computational basis ket splits as a tensor over the two factors:
    the combined index `tensorIndexEquiv j k ⟨a, b⟩` denotes `❘a⟩ ⊗ₛ ❘b⟩`. -/
theorem QState.basis_tensor_split {j k : ℕ} (a : Fin (2^j)) (b : Fin (2^k)) :
    (❘tensorIndexEquiv j k ⟨a, b⟩⟩ : QState (j + k)) ≈ (❘a⟩ : QState j) ⊗ₛ (❘b⟩ : QState k) := by
  simp only [QState.Equiv, QState.eval_basis, QState.eval_tensor, ket_tensorState]

-- ── Circuit.Equiv via symbolic states ─────────────────────────────────────────

/-- Equivalent circuits act identically on every symbolic state expression. -/
theorem Circuit.Equiv.apply_state {n : ℕ} {c₁ c₂ : Circuit n}
    (h : c₁ ≈ c₂) (s : QState n) : c₁ * s ≈ c₂ * s := by
  simp only [QState.Equiv, QState.eval_apply]; rw [h]

/-- Two circuits are equivalent iff they act identically on every symbolic basis ket. -/
theorem Circuit.Equiv.basis_iff_state {n : ℕ} (c₁ c₂ : Circuit n) :
    c₁ ≈ c₂ ↔ ∀ i : Fin (2^n), c₁ * ❘i⟩ ≈ c₂ * ❘i⟩ := by
  rw [Circuit.Equiv.basis_iff]
  simp [QState.Equiv, QState.eval_apply, QState.eval_basis]

/-- Two circuits are equivalent iff they act identically on every symbolic state expression.
    The basis-indexed form is usually more convenient; this stronger form avoids index-chasing
    when the input state is already in symbolic normal form. -/
theorem Circuit.Equiv.equiv_iff_all_states {n : ℕ} (c₁ c₂ : Circuit n) :
    c₁ ≈ c₂ ↔ ∀ s : QState n, c₁ * s ≈ c₂ * s :=
  ⟨fun h s => by simp only [QState.Equiv, QState.eval_apply]; rw [h],
   fun h => (basis_iff_state c₁ c₂).mpr (fun i => h ❘i⟩)⟩

/-- Two `(j+k)`-qubit circuits are equivalent iff they act identically on every
    factored basis state `❘a⟩ ⊗ₛ ❘b⟩`, looping over the basis of each factor.
    More convenient than `basis_iff_state` when the available gate-action lemmas are
    phrased on tensor factors (e.g. `CNOTGate_basis_tensor`, `RzGate_basis`). -/
theorem Circuit.Equiv.basis_iff_tensor {j k : ℕ} (c₁ c₂ : Circuit (j + k)) :
    c₁ ≈ c₂ ↔ ∀ (a : Fin (2^j)) (b : Fin (2^k)),
      c₁ * ((❘a⟩ : QState j) ⊗ₛ (❘b⟩ : QState k)) ≈ c₂ * ((❘a⟩ : QState j) ⊗ₛ (❘b⟩ : QState k)) := by
  constructor
  · intro h a b
    exact Circuit.Equiv.apply_state h _
  · intro h
    rw [basis_iff_state]
    intro i
    obtain ⟨⟨a, b⟩, rfl⟩ := (tensorIndexEquiv j k).surjective i
    calc c₁ * ❘tensorIndexEquiv j k ⟨a, b⟩⟩
        ≈ c₁ * ((❘a⟩ : QState j) ⊗ₛ (❘b⟩ : QState k)) :=
          QState.Equiv.apply_congr (QState.basis_tensor_split a b)
      _ ≈ c₂ * ((❘a⟩ : QState j) ⊗ₛ (❘b⟩ : QState k)) := h a b
      _ ≈ c₂ * ❘tensorIndexEquiv j k ⟨a, b⟩⟩ :=
          QState.Equiv.apply_congr (QState.basis_tensor_split a b).symm

end  -- noncomputable

end QLean
