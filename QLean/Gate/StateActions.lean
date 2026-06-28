import QLean.Gate.Standard
import QLean.State.Rewrite
import QLean.Circuit.Embed

open scoped QLean.Notation

namespace QLean

noncomputable section

-- ── Single-qubit gate actions on symbolic states ──────────────────────────────

-- A bare-numeral ket `❘0⟩` is `QState.basis (0 : Fin (2^n))`, whose `OfNat` instance is
-- stuck while `n` is a metavariable, so the gate-applied ket carries a `: QState 1`
-- annotation to pin `n`. Variable-index kets (`❘a⟩`, `a : Fin (2^1)`) infer `n` from the
-- index type and need none.
--
-- In each proof, `simp only` reduces to the QVector level; `exact` then closes the goal by
-- definitional equality (handling `Fin (2^1) = Fin 2`).

theorem XGate_bit0 : XGate * (❘0⟩ : QState 1) ≈ ❘1⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QCircuit.eval_gate]
  exact X_ket_zero

theorem XGate_bit1 : XGate * (❘1⟩ : QState 1) ≈ ❘0⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QCircuit.eval_gate]
  exact X_ket_one

theorem YGate_bit0 : YGate * (❘0⟩ : QState 1) ≈ Complex.I • ❘1⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             QCircuit.eval_gate]
  exact Y_ket_zero

theorem YGate_bit1 : YGate * (❘1⟩ : QState 1) ≈ (-Complex.I) • ❘0⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             QCircuit.eval_gate]
  exact Y_ket_one

theorem ZGate_bit0 : ZGate * (❘0⟩ : QState 1) ≈ ❘0⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QCircuit.eval_gate]
  exact Z_ket_zero

theorem ZGate_bit1 : ZGate * (❘1⟩ : QState 1) ≈ (-1 : ℂ) • ❘1⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             QCircuit.eval_gate]
  exact Z_ket_one

theorem SGate_bit0 : SGate * (❘0⟩ : QState 1) ≈ ❘0⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QCircuit.eval_gate]
  exact S_ket_zero

theorem SGate_bit1 : SGate * (❘1⟩ : QState 1) ≈ Complex.I • ❘1⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             QCircuit.eval_gate]
  exact S_ket_one

-- `((Real.sqrt 2)⁻¹ : ℂ)` is `(↑(Real.sqrt 2))⁻¹`, whereas `H_ket_zero` uses ℝ-smul by
-- `(Real.sqrt 2)⁻¹`. `← Complex.ofReal_inv` rewrites `(↑r)⁻¹ → ↑(r⁻¹)`, after which
-- `exact H_ket_zero` closes the goal (ℂ-smul by `↑r` is defeq to ℝ-smul by `r`).
theorem HGate_bit0 :
    HGate * (❘0⟩ : QState 1) ≈ ((Real.sqrt 2)⁻¹ : ℂ) • (❘0⟩ + ❘1⟩) := by
  simp only [QState.Equiv, QState.eval_apply, QCircuit.eval_gate, QState.eval_smul,
             QState.eval_add, QState.eval_basis, ← Complex.ofReal_inv]
  exact H_ket_zero

theorem HGate_bit1 :
    HGate * (❘1⟩ : QState 1) ≈ ((Real.sqrt 2)⁻¹ : ℂ) • (❘0⟩ + (-1 : ℂ) • ❘1⟩) := by
  simp only [QState.Equiv, QState.eval_apply, QCircuit.eval_gate, QState.eval_smul,
             QState.eval_add, QState.eval_basis, ← Complex.ofReal_inv]
  exact H_ket_one

/-- `Rz θ` acts on the basis tensor `❘a⟩` by the complex phase `exp((2a-1)·iθ/2)`:
    `exp(-iθ/2)` on `❘0⟩` and `exp(iθ/2)` on `❘1⟩`.
    `a : Fin (2^1)` matches the ket index directly. -/
theorem RzGate_basis (θ : ℝ) (a : Fin (2^1)) :
    RzGate θ * ❘a⟩
      ≈ Complex.exp ((2 * (a.val : ℂ) - 1) * Complex.I * θ / 2) • ❘a⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_basis, QState.eval_smul,
             QCircuit.eval_gate]
  -- `omega` can't evaluate the `Fin (2^1)` literals (the `2^1` modulus stays opaque),
  -- so split with `fin_cases`, which reduces `Fin (2^1)` definitionally to `Fin 2`.
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl
  · rw [Rz_ket_zero]; norm_num
  · rw [Rz_ket_one]; norm_num

-- ── Two-qubit gate actions ─────────────────────────────────────────────────────

/-- CNOT maps `❘a⟩ ⊗ ❘b⟩` to `❘a⟩ ⊗ |a+b⟩` (XOR on the target qubit).
    Variables have type `Fin (2^1)` so they directly match the ket index type. -/
theorem CNOTGate_basis_tensor (a b : Fin (2^1)) :
    CNOTGate * (❘a⟩ ⊗ ❘b⟩) ≈ ❘a⟩ ⊗ ❘a + b⟩ := by
  simp only [QState.Equiv, QState.eval_apply, QState.eval_tensor, QState.eval_basis,
             QCircuit.eval_gate, ket_tensorState]
  exact CNOT_ket_pair a b

-- ── Embedded gate actions in phase form (entry points for positional layers) ───
-- These lift the gate-agnostic `QCircuit.embed_single_action` / `embed_diag_action` to the two
-- specific gates an algorithm like the QFT addresses positionally, resolving the gate's matrix
-- entries to explicit phases once and for all. Downstream proofs then stay in the `QState` layer.

/-- A Hadamard embedded at the single qubit `qs 0` splits a basis ket into the equal superposition
    that clears / sets that qubit, the `❘1⟩` branch carrying the bit's sign as the phase
    `e^{2πi·b/2} = (-1)ᵇ` (where `b = selectIdx qs x` is the current bit). The phase-form lift of
    `embed_single_action` for `H`. -/
theorem embed_H_action {n : ℕ} (qs : Fin 1 ↪ Fin n) (x : Fin (2 ^ n)) :
    QCircuit.embed qs HGate * (❘x⟩ : QState n)
      ≈ ((Real.sqrt 2)⁻¹ : ℂ) • ❘mergeBits qs x 0⟩
        + (((Real.sqrt 2)⁻¹ : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * ((selectIdx qs x).val : ℂ) / 2))
          • ❘mergeBits qs x 1⟩ := by
  refine (QCircuit.embed_single_action qs H x).trans ?_
  rw [H_row0, H_row1]

/-- An embedded controlled-`Rₖ` (between the two qubits addressed by `qs`) is diagonal: it scales a
    basis ket by `e^{2πi/2ᵏ}` exactly when both addressed qubits are set (`selectIdx qs x = 3`), and
    fixes it otherwise. The phase-form lift of `embed_diag_action` for `controlled (Rk k)`. -/
theorem embed_controlled_Rk_action {n : ℕ} (qs : Fin 2 ↪ Fin n) (k : ℕ) (x : Fin (2 ^ n)) :
    QCircuit.embed qs (ControlledGate (Rk k)) * (❘x⟩ : QState n)
      ≈ (if selectIdx qs x = 3 then Complex.exp (2 * Real.pi * Complex.I / (2:ℂ) ^ k) else 1)
        • ❘x⟩ := by
  refine (QCircuit.embed_diag_action qs (controlled_isDiag (Rk_isDiag k)) x).trans ?_
  rw [controlled_Rk_diag]

end

end QLean
