import QLean
import Examples.PauliAlgebra
import Examples.RotationIdentities

/-!
# Controlled-Rz decomposition and CNOT commutation

Two parametric-angle facts about rotations against CNOT (Fenner Ex 13.2(2); N&C
Ex 4.31 eq. 4.39):

* **`C-Rz(φ) = (1 ⊗ Rz(φ/2)) · CNOT · (1 ⊗ Rz(−φ/2)) · CNOT`** — the workhorse
  decomposition every compiler uses to implement controlled rotations from CNOTs.
  When the control is `❘0⟩` the two Rz phases on the target cancel; when it is `❘1⟩`
  the intermediate X-flips make them add to the `Rz(φ)` phase.

* **`(1 ⊗ Rx(θ)) · CNOT = CNOT · (1 ⊗ Rx(θ))`** — Rx commutes with CNOT through the
  *target* (the dual of `Examples/RzCNOT.lean`, where Rz commutes through the control),
  because X-conjugation fixes Rx: `X · Rx(θ) · X ≈ Rx(θ)`.
-/

open scoped QLean.Notation

set_option linter.unnecessarySeqFocus false

namespace QLean.Examples

open QLean

noncomputable section

local notation "id1" => (1 : QCircuit 1)

-- exp-product helpers (duplicated from `RotationIdentities` where they are private)
private lemma one_eq_exp_mul {a b : ℂ} (h : a + b = 0) :
    (1 : ℂ) = Complex.exp a * Complex.exp b := by
  rw [← Complex.exp_add, h, Complex.exp_zero]

private lemma exp_eq_exp_mul {c a b : ℂ} (h : a + b = c) :
    Complex.exp c = Complex.exp a * Complex.exp b := by
  rw [← Complex.exp_add, h]

/-- `X · Rx(θ) · X ≈ Rx(θ)`: X fixes X-rotations under conjugation (shared axis). -/
theorem x_rx_x (θ : ℝ) : XGate * RxGate θ * XGate ≈ RxGate θ := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, XGate_bit0, RxGate_bit1,
         QCircuit.apply_add, QCircuit.apply_smul, QCircuit.apply_smul,
         XGate_bit0, XGate_bit1, RxGate_bit0, QState.add_comm]
  · grw [QCircuit.seq_action, QCircuit.seq_action, XGate_bit1, RxGate_bit0,
         QCircuit.apply_add, QCircuit.apply_smul, QCircuit.apply_smul,
         XGate_bit0, XGate_bit1, RxGate_bit1, QState.add_comm]

/-- Rx commutes with CNOT through the target qubit (N&C eq. 4.39). -/
theorem rx_commutes_cnot_target (θ : ℝ) :
    (id1 ⊗ RxGate θ) * CNOTGate ≈ CNOTGate * (id1 ⊗ RxGate θ) := by
  -- `X (Rx s) ≈ Rx (X s)` in action form, from `x_rx_x`
  have h : XGate * RxGate θ ≈ RxGate θ * XGate := by
    calc XGate * RxGate θ
        ≈ XGate * RxGate θ * (XGate * XGate) := by
          grw [x_mul_x, QCircuit.seq_id_right]
      _ ≈ (XGate * RxGate θ * XGate) * XGate := by
          simp only [QCircuit.Equiv, QCircuit.eval_seq, mul_assoc]
      _ ≈ RxGate θ * XGate := by grw [x_rx_x]
  have comm : ∀ s : QState 1, XGate * (RxGate θ * s) ≈ RxGate θ * (XGate * s) := fun s =>
    (QCircuit.seq_action _ _ _).symm.trans ((h.apply_state s).trans (QCircuit.seq_action _ _ _))
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_zero,
         QCircuit.par_action_tensor, QCircuit.id_action, CNOTGate_zero]
  · grw [QCircuit.seq_action, QCircuit.seq_action, CNOTGate_one,
         QCircuit.par_action_tensor, QCircuit.id_action, QCircuit.par_action_tensor,
         QCircuit.id_action, CNOTGate_one, comm]

-- ── The controlled-Rz decomposition (Fenner Ex 13.2(2)) ───────────────────────

/-- `C-Rz(φ) ≈ (1 ⊗ Rz(φ/2)) · CNOT · (1 ⊗ Rz(−φ/2)) · CNOT`. -/
theorem controlled_rz_decomp (φ : ℝ) :
    ControlledGate (Rz φ)
      ≈ (id1 ⊗ RzGate (φ/2)) * CNOTGate * (id1 ⊗ RzGate (-φ/2)) * CNOTGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
  -- In each case: expand the RHS ladder first (the LHS controlled gate stays folded
  -- until the end), collect both sides into `scalar • (❘a⟩ ⊗ ❘b⟩)`, then compare
  -- exponential arguments.
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.seq_action,
         CNOTGate_basis_tensor 0 0, show (0 : Fin (2^1)) + 0 = 0 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, RzGate_basis,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 0 0,
         show (0 : Fin (2^1)) + 0 = 0 by decide,
         QCircuit.apply_smul, QCircuit.par_action_tensor, QCircuit.id_action,
         RzGate_basis, QState.tensor_smul_right, QState.smul_smul,
         ControlledGate_zero (Rz φ)]
    exact (QState.one_smul _).symm.trans
      (QState.smul_scalar_congr (one_eq_exp_mul (by norm_num <;> ring)) _)
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.seq_action,
         CNOTGate_basis_tensor 0 1, show (0 : Fin (2^1)) + 1 = 1 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, RzGate_basis,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 0 1,
         show (0 : Fin (2^1)) + 1 = 1 by decide,
         QCircuit.apply_smul, QCircuit.par_action_tensor, QCircuit.id_action,
         RzGate_basis, QState.tensor_smul_right, QState.smul_smul,
         ControlledGate_zero (Rz φ)]
    exact (QState.one_smul _).symm.trans
      (QState.smul_scalar_congr (one_eq_exp_mul (by norm_num <;> ring)) _)
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.seq_action,
         CNOTGate_basis_tensor 1 0, show (1 : Fin (2^1)) + 0 = 1 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, RzGate_basis,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 1 1,
         show (1 : Fin (2^1)) + 1 = 0 by decide,
         QCircuit.apply_smul, QCircuit.par_action_tensor, QCircuit.id_action,
         RzGate_basis, QState.tensor_smul_right, QState.smul_smul,
         ControlledGate_one (Rz φ), RzGate_basis, QState.tensor_smul_right]
    exact QState.smul_scalar_congr (exp_eq_exp_mul (by norm_num <;> ring)) _
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.seq_action,
         CNOTGate_basis_tensor 1 1, show (1 : Fin (2^1)) + 1 = 0 by decide,
         QCircuit.par_action_tensor, QCircuit.id_action, RzGate_basis,
         QState.tensor_smul_right, QCircuit.apply_smul, CNOTGate_basis_tensor 1 0,
         show (1 : Fin (2^1)) + 0 = 1 by decide,
         QCircuit.apply_smul, QCircuit.par_action_tensor, QCircuit.id_action,
         RzGate_basis, QState.tensor_smul_right, QState.smul_smul,
         ControlledGate_one (Rz φ), RzGate_basis, QState.tensor_smul_right]
    exact QState.smul_scalar_congr (exp_eq_exp_mul (by norm_num <;> ring)) _

end

end QLean.Examples
