import QLean.State.Semantics
import Mathlib.Tactic.GCongr

open scoped QLean.Notation

namespace QLean

namespace QState

noncomputable section

-- ── QState.Equiv ──────────────────────────────────────────────────────────────

/-- Two state expressions are equivalent if they denote the same vector. -/
def Equiv (s t : QState n) : Prop := eval s = eval t

@[reducible] instance : HasEquiv (QState n) := ⟨Equiv⟩

@[refl]  theorem Equiv.refl  (s : QState n) : s ≈ s := rfl
@[symm]  theorem Equiv.symm  {s t : QState n} : s ≈ t → t ≈ s := Eq.symm
@[trans] theorem Equiv.trans {s t u : QState n} : s ≈ t → t ≈ u → s ≈ u := Eq.trans

instance : Trans (@Equiv n) (@Equiv n) (@Equiv n) :=
  ⟨Equiv.trans⟩

-- ── Congruence lemmas ─────────────────────────────────────────────────────────

@[gcongr]
theorem Equiv.apply_congr {C : QCircuit n} {s t : QState n}
    (h : s ≈ t) : C * s ≈ C * t := by
  simp only [Equiv, eval_apply]; rw [h]

@[gcongr]
theorem Equiv.add_congr {s s' t t' : QState n}
    (hs : s ≈ s') (ht : t ≈ t') : s + t ≈ s' + t' := by
  simp only [Equiv, eval_add]; rw [hs, ht]

@[gcongr]
theorem Equiv.smul_congr {s s' : QState n} (α : ℂ)
    (hs : s ≈ s') : α • s ≈ α • s' := by
  simp only [Equiv, eval_smul]; rw [hs]

@[gcongr]
theorem Equiv.tensor_congr {s s' : QState j} {t t' : QState k}
    (hs : s ≈ s') (ht : t ≈ t') : s ⊗ t ≈ s' ⊗ t' := by
  simp only [Equiv, eval_tensor]; rw [hs, ht]

-- ── Scalar algebra ────────────────────────────────────────────────────────────
-- `QState.smul` is a bare `SMul` (a raw constructor), so the `MulAction`/`Module`
-- lemmas (`one_smul`, `smul_smul`, …) do not fire on it. These `≈` lemmas recover
-- the scalar algebra in the symbolic layer.

theorem one_smul (s : QState n) : (1 : ℂ) • s ≈ s := by
  simp only [Equiv, eval_smul, _root_.one_smul]

theorem smul_smul (a b : ℂ) (s : QState n) : a • (b • s) ≈ (a * b) • s := by
  simp only [Equiv, eval_smul, _root_.smul_smul]

theorem smul_add (a : ℂ) (s t : QState n) : a • (s + t) ≈ a • s + a • t := by
  simp only [Equiv, eval_smul, eval_add, _root_.smul_add]

/-- Rewrite a scalar factor by a ℂ-equality: the finishing move when a `grw` chain has
    reduced both sides to `α • s` and `β • s` with `α = β` a numeric fact. -/
theorem smul_scalar_congr {α β : ℂ} (h : α = β) (s : QState n) : α • s ≈ β • s := by
  rw [h]

-- ── Additive commutativity/associativity (modulo ≈) ──────────────────────────
-- `QState.add` is a raw constructor, so the additive-monoid lemmas do not fire on it.

theorem add_comm (s t : QState n) : s + t ≈ t + s := by
  simp only [Equiv, eval_add]; exact _root_.add_comm _ _

theorem add_assoc (s t u : QState n) : s + t + u ≈ s + (t + u) := by
  simp only [Equiv, eval_add]; exact _root_.add_assoc _ _ _

-- ── Distributivity rules ──────────────────────────────────────────────────────

theorem add_tensor_left (s t : QState j) (u : QState k) :
    (s + t) ⊗ u ≈ s ⊗ u + t ⊗ u := by
  simp only [Equiv, eval_tensor, eval_add, tensorState_add_left]

theorem tensor_add_right (s : QState j) (t u : QState k) :
    s ⊗ (t + u) ≈ s ⊗ t + s ⊗ u := by
  simp only [Equiv, eval_tensor, eval_add, tensorState_add_right]

theorem smul_tensor_left (α : ℂ) (s : QState j) (t : QState k) :
    (α • s) ⊗ t ≈ α • (s ⊗ t) := by
  simp only [Equiv, eval_tensor, eval_smul, tensorState_smul_left]

theorem tensor_smul_right (α : ℂ) (s : QState j) (t : QState k) :
    s ⊗ (α • t) ≈ α • (s ⊗ t) := by
  simp only [Equiv, eval_tensor, eval_smul, tensorState_smul_right]

-- ── Tensor algebra and basis splits ───────────────────────────────────────────

/-- Tensor product of state expressions is associative (right-unit case).
    Both sides have type `QState (j + k + 1)` since `(j+k)+1 = j+(k+1)` definitionally. -/
theorem tensor_assoc {j k : ℕ} (s : QState j) (t : QState k) (u : QState 1) :
    (s ⊗ t) ⊗ u ≈ (s ⊗ (t ⊗ u) : QState (j + (k + 1))) := by
  simp only [Equiv, eval_tensor, tensorState_assoc_one]

/-- The all-zero basis ket splits as a tensor of all-zero kets. -/
theorem ket_zero_tensor (j k : ℕ) :
    (❘0⟩ : QState (j + k)) ≈ (❘0⟩ : QState j) ⊗ (❘0⟩ : QState k) := by
  simp only [Equiv, eval_basis, eval_tensor, ket_tensorState]
  congr 1

/-- A computational basis ket splits as a tensor over the two factors:
    the combined index `tensorIndexEquiv j k ⟨a, b⟩` denotes `❘a⟩ ⊗ ❘b⟩`. -/
theorem basis_tensor_split {j k : ℕ} (a : Fin (2^j)) (b : Fin (2^k)) :
    ❘tensorIndexEquiv j k ⟨a, b⟩⟩ ≈ ❘a⟩ ⊗ ❘b⟩ := by
  simp only [Equiv, eval_basis, eval_tensor, ket_tensorState]

/-- The all-ones ket on `n+1` qubits splits as the all-ones ket on the low `n` qubits
    tensored with `❘1⟩` on the top qubit: `|1…1⟩ ≈ |1…1⟩ ⊗ ❘1⟩`. The companion of
    `ket_zero_tensor` for the all-ones basis state. -/
theorem allOnes_succ (n : ℕ) :
    (❘allOnes (n + 1)⟩ : QState (n + 1)) ≈ ❘allOnes n⟩ ⊗ ❘(1 : Fin (2^1))⟩ := by
  have key : allOnes (n + 1) = tensorIndexEquiv n 1 ⟨allOnes n, (1 : Fin (2^1))⟩ := by
    apply Fin.ext
    rw [tensorIndexEquiv_apply_val, allOnes_val, allOnes_val]
    have h : 0 < 2 ^ n := pow_pos (by norm_num) n
    have h1 : (1 : Fin (2^1)).val = 1 := rfl
    rw [h1, pow_succ]; omega
  rw [key]
  exact basis_tensor_split (allOnes n) (1 : Fin (2^1))

end  -- noncomputable

end QState

end QLean
