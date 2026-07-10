import QLean.Circuit.Semantics
import QLean.Basic.Hilbert
import QLean.State.Rewrite
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped QLean.Notation

namespace QLean

namespace QCircuit

noncomputable section

-- ── QCircuit.Equiv ─────────────────────────────────────────────────────────────

/-- Two circuits are equivalent if they evaluate to the same unitary. -/
def Equiv (c₁ c₂ : QCircuit n) : Prop := eval c₁ = eval c₂

-- `c₁ ≈ c₂` is notation for `QCircuit.Equiv c₁ c₂`.
@[reducible] instance : HasEquiv (QCircuit n) := ⟨Equiv⟩

@[refl]  theorem Equiv.refl  (c : QCircuit n) : c ≈ c := rfl
@[symm]  theorem Equiv.symm  {c₁ c₂ : QCircuit n} : c₁ ≈ c₂ → c₂ ≈ c₁ :=
  Eq.symm
@[trans] theorem Equiv.trans {c₁ c₂ c₃ : QCircuit n} :
    c₁ ≈ c₂ → c₂ ≈ c₃ → c₁ ≈ c₃ := Eq.trans

instance : Trans (@Equiv n) (@Equiv n) (@Equiv n) :=
  ⟨Equiv.trans⟩

-- ── Congruence lemmas ─────────────────────────────────────────────────────────

/-- Equivalent components yield equivalent sequential circuits. -/
@[gcongr]
theorem Equiv.seq_congr {c₁ c₁' c₂ c₂' : QCircuit n}
    (h₁ : c₁ ≈ c₁') (h₂ : c₂ ≈ c₂') :
    c₁ * c₂ ≈ c₁' * c₂' := by
  simp only [Equiv, eval_seq]; rw [h₁, h₂]

/-- Equivalent components yield equivalent parallel circuits. -/
@[gcongr]
theorem Equiv.par_congr {c₁ c₁' : QCircuit j} {c₂ c₂' : QCircuit k}
    (h₁ : c₁ ≈ c₁') (h₂ : c₂ ≈ c₂') :
    c₁ ⊗ c₂ ≈ c₁' ⊗ c₂' := by
  simp only [Equiv, eval_par]; rw [h₁, h₂]

-- ── Basic rewrite rules ───────────────────────────────────────────────────────

/-- `id` is a left identity for sequential composition. -/
theorem seq_id_left (c : QCircuit n) : (1 : QCircuit n) * c ≈ c := by
  simp [Equiv]

/-- `id` is a right identity for sequential composition. -/
theorem seq_id_right (c : QCircuit n) : c * (1 : QCircuit n) ≈ c := by
  simp [Equiv]

/-- Sequential composition is associative. -/
theorem seq_assoc (c₁ c₂ c₃ : QCircuit n) :
    (c₁ * c₂) * c₃ ≈ c₁ * (c₂ * c₃) := by
  simp [Equiv, mul_assoc]

/-- A gate carrying a matrix product is the sequence of the factor gates. -/
theorem gate_seq (M N : QMatrix n) :
    (QCircuit.gate (M * N) : QCircuit n) ≈ QCircuit.gate M * QCircuit.gate N := by
  simp [Equiv]

-- ── par_assoc ─────────────────────────────────────────────────────────────────

/-- Parallel composition is associative up to `castN` and `≈`. -/
theorem par_assoc (c₁ : QCircuit j) (c₂ : QCircuit k) (c₃ : QCircuit l) :
    castN (Nat.add_assoc j k l) ((c₁ ⊗ c₂) ⊗ c₃) ≈ c₁ ⊗ (c₂ ⊗ c₃) := by
  simp only [Equiv, eval_castN, eval_par]
  exact kron_assoc (eval c₁) (eval c₂) (eval c₃)

-- ── Global-phase equivalence ──────────────────────────────────────────────────

/-- Two circuits are equivalent up to a global phase: their evaluations differ by a unit
    scalar `e^{iγ}`. Many textbook identities (`T ∼ Rz (π/4)`, `X ∼ Rx π`, `HTH ∼ Rx (π/4)`)
    hold only in this sense — the phase is unobservable, but the matrices differ. -/
def PhaseEquiv (c₁ c₂ : QCircuit n) : Prop :=
  ∃ γ : ℝ, eval c₁ = Complex.exp (γ * Complex.I) • eval c₂

theorem PhaseEquiv.refl (c : QCircuit n) : PhaseEquiv c c :=
  ⟨0, by simp⟩

/-- Strict equivalence implies phase equivalence (with phase `0`). -/
theorem PhaseEquiv.of_equiv {c₁ c₂ : QCircuit n} (h : c₁ ≈ c₂) : PhaseEquiv c₁ c₂ :=
  ⟨0, by simpa using h⟩

theorem PhaseEquiv.symm {c₁ c₂ : QCircuit n} : PhaseEquiv c₁ c₂ → PhaseEquiv c₂ c₁ := by
  rintro ⟨γ, h⟩
  refine ⟨-γ, ?_⟩
  rw [h, smul_smul, ← Complex.exp_add]
  have : ((-γ : ℝ) : ℂ) * Complex.I + (γ : ℝ) * Complex.I = 0 := by push_cast; ring
  rw [this, Complex.exp_zero, one_smul]

theorem PhaseEquiv.trans {c₁ c₂ c₃ : QCircuit n} :
    PhaseEquiv c₁ c₂ → PhaseEquiv c₂ c₃ → PhaseEquiv c₁ c₃ := by
  rintro ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  refine ⟨γ₁ + γ₂, ?_⟩
  rw [h₁, h₂, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- Sequencing phase-equivalent circuits is phase-equivalent: the phases add. -/
theorem PhaseEquiv.seq_congr {c₁ c₁' c₂ c₂' : QCircuit n}
    (h₁ : PhaseEquiv c₁ c₁') (h₂ : PhaseEquiv c₂ c₂') :
    PhaseEquiv (c₁ * c₂) (c₁' * c₂') := by
  obtain ⟨γ₁, e₁⟩ := h₁; obtain ⟨γ₂, e₂⟩ := h₂
  refine ⟨γ₁ + γ₂, ?_⟩
  simp only [eval_seq, e₁, e₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- Establish phase equivalence from the basis actions: if `c₁` acts on every basis ket
    as `e^{iγ}` times the `c₂` action, then `c₁ ≈ₚ c₂`. The `PhaseEquiv` analogue of
    `Equiv.basis_iff_state`, letting phase-equivalence proofs stay in the `QState` layer. -/
theorem PhaseEquiv.of_basis {n : ℕ} {c₁ c₂ : QCircuit n} (γ : ℝ)
    (h : ∀ i : Fin (2^n), c₁ * (❘i⟩ : QState n)
          ≈ Complex.exp (γ * Complex.I) • (c₂ * ❘i⟩)) :
    PhaseEquiv c₁ c₂ := by
  refine ⟨γ, ?_⟩
  ext r i
  have hh := h i
  simp only [QState.Equiv, QState.eval_apply, QState.eval_smul, QState.eval_basis] at hh
  have := congr_fun (congr_fun hh r) 0
  simpa [mul_ket_apply, Matrix.smul_apply] using this

end  -- noncomputable (temporarily closed for notation; reopened below)

end QCircuit

namespace Notation

/-- `c₁ ≈ₚ c₂`: circuit equivalence up to a global phase. -/
scoped infix:50 " ≈ₚ " => QLean.QCircuit.PhaseEquiv

end Notation

namespace QCircuit

noncomputable section

-- ── Basis characterization ───────────────────────────────────────────────────

/-- Two circuits are equivalent iff they act identically on every computational basis state. -/
theorem Equiv.basis_iff {n : ℕ} (c₁ c₂ : QCircuit n) :
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
theorem interchange_law {j k : ℕ} (a b : QCircuit j) (c d : QCircuit k) :
    (a * b) ⊗ (c * d) ≈ (a ⊗ c) * (b ⊗ d) := by
  simp [Equiv, ← kron_mul]

-- ── QCircuit action on symbolic states ────────────────────────────────────────
-- The lemmas below reshape an `apply` expression `C * s`; they build on the
-- `QState.Equiv` machinery in `State/Rewrite`, which this module imports.

/-- A circuit distributes over state addition. -/
theorem apply_add (C : QCircuit n) (s t : QState n) :
    C * (s + t) ≈ C * s + C * t := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_add, Matrix.mul_add]

/-- A circuit commutes with scalar multiplication. -/
theorem apply_smul (C : QCircuit n) (α : ℂ) (s : QState n) :
    C * (α • s) ≈ α • (C * s) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_smul, Matrix.mul_smul]

/-- Sequential circuit composition associates with state application:
    applying `c₁ * c₂` (first c₂, then c₁) to s equals first applying c₂ to s,
    then applying c₁ to the result. -/
theorem seq_action (c₁ c₂ : QCircuit n) (s : QState n) :
    (c₁ * c₂) * s ≈ c₁ * (c₂ * s) := by
  simp only [QState.Equiv, QState.eval_apply, eval_seq, Matrix.mul_assoc]

/-- The identity circuit acts trivially. -/
theorem id_action (s : QState n) : (1 : QCircuit n) * s ≈ s := by
  simp only [QState.Equiv, QState.eval_apply, eval_id, Matrix.one_mul]

/-- Parallel circuits act componentwise on tensor-product states. -/
theorem par_action_tensor (c₁ : QCircuit j) (c₂ : QCircuit k)
    (s : QState j) (t : QState k) :
    (c₁ ⊗ c₂) * (s ⊗ t) ≈ (c₁ * s) ⊗ (c₂ * t) := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_tensor, eval_par, kron_tensorState]

-- ── Symbolic-state equivalence criteria ───────────────────────────────────────
-- These characterize `QCircuit.Equiv` through the symbolic `QState` layer (building on
-- `State/Rewrite`), so they sit here alongside `basis_iff`.

/-- Equivalent circuits act identically on every symbolic state expression. -/
theorem Equiv.apply_state {n : ℕ} {c₁ c₂ : QCircuit n}
    (h : c₁ ≈ c₂) (s : QState n) : c₁ * s ≈ c₂ * s := by
  simp only [QState.Equiv, QState.eval_apply]; rw [h]

/-- Two circuits are equivalent iff they act identically on every symbolic basis ket. -/
theorem Equiv.basis_iff_state {n : ℕ} (c₁ c₂ : QCircuit n) :
    c₁ ≈ c₂ ↔ ∀ i : Fin (2^n), c₁ * ❘i⟩ ≈ c₂ * ❘i⟩ := by
  rw [Equiv.basis_iff]
  simp [QState.Equiv, QState.eval_apply, QState.eval_basis]

/-- Two circuits are equivalent iff they act identically on every symbolic state expression.
    The basis-indexed form is usually more convenient; this stronger form avoids index-chasing
    when the input state is already in symbolic normal form. -/
theorem Equiv.equiv_iff_all_states {n : ℕ} (c₁ c₂ : QCircuit n) :
    c₁ ≈ c₂ ↔ ∀ s : QState n, c₁ * s ≈ c₂ * s :=
  ⟨fun h s => by simp only [QState.Equiv, QState.eval_apply]; rw [h],
   fun h => (basis_iff_state c₁ c₂).mpr (fun i => h ❘i⟩)⟩

/-- Two `(j+k)`-qubit circuits are equivalent iff they act identically on every
    factored basis state `❘a⟩ ⊗ ❘b⟩`, looping over the basis of each factor.
    More convenient than `basis_iff_state` when the available gate-action lemmas are
    phrased on tensor factors (e.g. `CNOTGate_basis_tensor`, `RzGate_basis`). -/
theorem Equiv.basis_iff_tensor {j k : ℕ} (c₁ c₂ : QCircuit (j + k)) :
    c₁ ≈ c₂ ↔ ∀ (a : Fin (2^j)) (b : Fin (2^k)),
      c₁ * (❘a⟩ ⊗ ❘b⟩) ≈ c₂ * (❘a⟩ ⊗ ❘b⟩) := by
  constructor
  · intro h a b
    exact Equiv.apply_state h _
  · intro h
    rw [basis_iff_state]
    intro i
    obtain ⟨⟨a, b⟩, rfl⟩ := (tensorIndexEquiv j k).surjective i
    calc c₁ * ❘tensorIndexEquiv j k ⟨a, b⟩⟩
        ≈ c₁ * (❘a⟩ ⊗ ❘b⟩) :=
          QState.Equiv.apply_congr (QState.basis_tensor_split a b)
      _ ≈ c₂ * (❘a⟩ ⊗ ❘b⟩) := h a b
      _ ≈ c₂ * ❘tensorIndexEquiv j k ⟨a, b⟩⟩ :=
          QState.Equiv.apply_congr (QState.basis_tensor_split a b).symm

end  -- noncomputable

end QCircuit

end QLean
