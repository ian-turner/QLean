import QLean.Circuit.Semantics
import QLean.Basic.Hilbert
import QLean.State.Rewrite
import Mathlib.Tactic.GCongr

open scoped QLean.Notation

namespace QLean

namespace Circuit

noncomputable section

-- ── Circuit.Equiv ─────────────────────────────────────────────────────────────

/-- Two circuits are equivalent if they evaluate to the same unitary. -/
def Equiv (c₁ c₂ : Circuit n) : Prop := eval c₁ = eval c₂

-- `c₁ ≈ c₂` is notation for `Circuit.Equiv c₁ c₂`.
@[reducible] instance : HasEquiv (Circuit n) := ⟨Equiv⟩

@[refl]  theorem Equiv.refl  (c : Circuit n) : c ≈ c := rfl
@[symm]  theorem Equiv.symm  {c₁ c₂ : Circuit n} : c₁ ≈ c₂ → c₂ ≈ c₁ :=
  Eq.symm
@[trans] theorem Equiv.trans {c₁ c₂ c₃ : Circuit n} :
    c₁ ≈ c₂ → c₂ ≈ c₃ → c₁ ≈ c₃ := Eq.trans

instance : Trans (@Equiv n) (@Equiv n) (@Equiv n) :=
  ⟨Equiv.trans⟩

-- ── Congruence lemmas ─────────────────────────────────────────────────────────

/-- Equivalent components yield equivalent sequential circuits. -/
@[gcongr]
theorem Equiv.seq_congr {c₁ c₁' c₂ c₂' : Circuit n}
    (h₁ : c₁ ≈ c₁') (h₂ : c₂ ≈ c₂') :
    c₁ * c₂ ≈ c₁' * c₂' := by
  simp only [Equiv, eval_seq]; rw [h₁, h₂]

/-- Equivalent components yield equivalent parallel circuits. -/
@[gcongr]
theorem Equiv.par_congr {c₁ c₁' : Circuit j} {c₂ c₂' : Circuit k}
    (h₁ : c₁ ≈ c₁') (h₂ : c₂ ≈ c₂') :
    c₁ ⊗ c₂ ≈ c₁' ⊗ c₂' := by
  simp only [Equiv, eval_par]; rw [h₁, h₂]

-- ── Basic rewrite rules ───────────────────────────────────────────────────────

/-- `id` is a left identity for sequential composition. -/
theorem seq_id_left (c : Circuit n) : (1 : Circuit n) * c ≈ c := by
  simp [Equiv]

/-- `id` is a right identity for sequential composition. -/
theorem seq_id_right (c : Circuit n) : c * (1 : Circuit n) ≈ c := by
  simp [Equiv]

/-- Sequential composition is associative. -/
theorem seq_assoc (c₁ c₂ c₃ : Circuit n) :
    (c₁ * c₂) * c₃ ≈ c₁ * (c₂ * c₃) := by
  simp [Equiv, mul_assoc]

-- ── par_assoc ─────────────────────────────────────────────────────────────────

/-- Parallel composition is associative up to `castN` and `≈`. -/
theorem par_assoc (c₁ : Circuit j) (c₂ : Circuit k) (c₃ : Circuit l) :
    castN (Nat.add_assoc j k l) ((c₁ ⊗ c₂) ⊗ c₃) ≈ c₁ ⊗ (c₂ ⊗ c₃) := by
  simp only [Equiv, eval_castN, eval_par]
  exact kron_assoc (eval c₁) (eval c₂) (eval c₃)

-- ── Basis characterization ───────────────────────────────────────────────────

private lemma mul_ket_apply {n : ℕ} (M : QMatrix n) (i r : Fin (2^n)) :
    (M * ket i) r 0 = M r i := by
  simp [Matrix.mul_apply, ket_apply, mul_ite, Finset.sum_ite_eq', Finset.mem_univ]

/-- Two circuits are equivalent iff they act identically on every computational basis state. -/
theorem Equiv.basis_iff {n : ℕ} (c₁ c₂ : Circuit n) :
    c₁ ≈ c₂ ↔ ∀ i : Fin (2^n), eval c₁ * ket i = eval c₂ * ket i := by
  simp only [Equiv]
  constructor
  · intro h i; rw [h]
  · intro h
    ext r c
    simpa [mul_ket_apply] using congr_fun (congr_fun (h c) r) 0

-- ── Interchange law ──────────────────────────────────────────────────────────

/-- Parallel composition distributes over sequential composition:
    running two sequences in parallel equals sequencing two parallel steps. -/
theorem interchange_law {j k : ℕ} (a b : Circuit j) (c d : Circuit k) :
    (a * b) ⊗ (c * d) ≈ (a ⊗ c) * (b ⊗ d) := by
  simp [Equiv, ← kron_mul]

-- ── Circuit action on symbolic states ────────────────────────────────────────
-- The lemmas below reshape an `apply` expression `C * s`; they build on the
-- `QState.Equiv` machinery in `State/Rewrite`, which this module imports.

/-- A circuit distributes over state addition. -/
theorem apply_add (C : Circuit n) (s t : QState n) :
    C * (s + t) ≈ C * s + C * t := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_add, Matrix.mul_add]

/-- A circuit commutes with scalar multiplication. -/
theorem apply_smul (C : Circuit n) (α : ℂ) (s : QState n) :
    C * (α • s) ≈ α • (C * s) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_smul, Matrix.mul_smul]

/-- Sequential circuit composition associates with state application:
    applying `c₁ * c₂` (first c₂, then c₁) to s equals first applying c₂ to s,
    then applying c₁ to the result. -/
theorem seq_action (c₁ c₂ : Circuit n) (s : QState n) :
    (c₁ * c₂) * s ≈ c₁ * (c₂ * s) := by
  simp only [QState.Equiv, QState.eval_apply, eval_seq, Matrix.mul_assoc]

/-- The identity circuit acts trivially. -/
theorem id_action (s : QState n) : (1 : Circuit n) * s ≈ s := by
  simp only [QState.Equiv, QState.eval_apply, eval_id, Matrix.one_mul]

/-- Parallel circuits act componentwise on tensor-product states. -/
theorem par_action_tensor (c₁ : Circuit j) (c₂ : Circuit k)
    (s : QState j) (t : QState k) :
    (c₁ ⊗ c₂) * (s ⊗ t) ≈ (c₁ * s) ⊗ (c₂ * t) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_tensor, eval_par, kron_tensorState]

-- ── Symbolic-state equivalence criteria ───────────────────────────────────────
-- These characterize `Circuit.Equiv` through the symbolic `QState` layer, so they
-- build on `State/Rewrite` (`QState.Equiv`, the `c * s` action). They live here,
-- next to `basis_iff`, rather than in `State/Rewrite`.

/-- Equivalent circuits act identically on every symbolic state expression. -/
theorem Equiv.apply_state {n : ℕ} {c₁ c₂ : Circuit n}
    (h : c₁ ≈ c₂) (s : QState n) : c₁ * s ≈ c₂ * s := by
  simp only [QState.Equiv, QState.eval_apply]; rw [h]

/-- Two circuits are equivalent iff they act identically on every symbolic basis ket. -/
theorem Equiv.basis_iff_state {n : ℕ} (c₁ c₂ : Circuit n) :
    c₁ ≈ c₂ ↔ ∀ i : Fin (2^n), c₁ * ❘i⟩ ≈ c₂ * ❘i⟩ := by
  rw [Equiv.basis_iff]
  simp [QState.Equiv, QState.eval_apply, QState.eval_basis]

/-- Two circuits are equivalent iff they act identically on every symbolic state expression.
    The basis-indexed form is usually more convenient; this stronger form avoids index-chasing
    when the input state is already in symbolic normal form. -/
theorem Equiv.equiv_iff_all_states {n : ℕ} (c₁ c₂ : Circuit n) :
    c₁ ≈ c₂ ↔ ∀ s : QState n, c₁ * s ≈ c₂ * s :=
  ⟨fun h s => by simp only [QState.Equiv, QState.eval_apply]; rw [h],
   fun h => (basis_iff_state c₁ c₂).mpr (fun i => h ❘i⟩)⟩

/-- Two `(j+k)`-qubit circuits are equivalent iff they act identically on every
    factored basis state `❘a⟩ ⊗ ❘b⟩`, looping over the basis of each factor.
    More convenient than `basis_iff_state` when the available gate-action lemmas are
    phrased on tensor factors (e.g. `CNOTGate_basis_tensor`, `RzGate_basis`). -/
theorem Equiv.basis_iff_tensor {j k : ℕ} (c₁ c₂ : Circuit (j + k)) :
    c₁ ≈ c₂ ↔ ∀ (a : Fin (2^j)) (b : Fin (2^k)),
      c₁ * ((❘a⟩ : QState j) ⊗ (❘b⟩ : QState k)) ≈ c₂ * ((❘a⟩ : QState j) ⊗ (❘b⟩ : QState k)) := by
  constructor
  · intro h a b
    exact Equiv.apply_state h _
  · intro h
    rw [basis_iff_state]
    intro i
    obtain ⟨⟨a, b⟩, rfl⟩ := (tensorIndexEquiv j k).surjective i
    calc c₁ * ❘tensorIndexEquiv j k ⟨a, b⟩⟩
        ≈ c₁ * ((❘a⟩ : QState j) ⊗ (❘b⟩ : QState k)) :=
          QState.Equiv.apply_congr (QState.basis_tensor_split a b)
      _ ≈ c₂ * ((❘a⟩ : QState j) ⊗ (❘b⟩ : QState k)) := h a b
      _ ≈ c₂ * ❘tensorIndexEquiv j k ⟨a, b⟩⟩ :=
          QState.Equiv.apply_congr (QState.basis_tensor_split a b).symm

end  -- noncomputable

end Circuit

end QLean
