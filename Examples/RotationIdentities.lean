import QLean
import Examples.PauliAlgebra

/-!
# Rotation-gate identities

The parametric-angle toolbox (N&C §4.2, Exercises 4.4/4.7/4.14/4.15; Fenner §8–9):

* additivity: `Ry(φ)·Ry(θ) ≈ Ry(θ+φ)`, `Rx(φ)·Rx(θ) ≈ Rx(θ+φ)` (the `Rz` case is
  `Examples/RzPlus.lean`), and the zero-rotations `≈ 1`
* X-conjugation flips the angle: `X·Ry(θ)·X ≈ Ry(−θ)`, `X·Rz(θ)·X ≈ Rz(−θ)`
* the global-phase family: `Z ≈ₚ Rz(π)`, `S ≈ₚ Rz(π/2)`, `T ≈ₚ Rz(π/4)`

Additivity and the zero-rotations are 1-qubit *parametric matrix atoms* (trig addition is
the irreducible content, so they are proved in `rz_plus` style at the matrix level); the
conjugation and phase results are `grw` chains over basis atoms.
-/

open scoped QLean.Notation

-- `norm_num <;> ring`-style closers trip this purely stylistic linter.
set_option linter.unnecessarySeqFocus false

namespace QLean.Examples

open QLean

noncomputable section

-- ── Additivity (N&C Ex 4.15 special cases; Fenner Ex 9.3(9)) ──────────────────

/-- `Ry(φ) · Ry(θ) ≈ Ry(θ+φ)`: Y-rotation angles add. -/
theorem ry_plus (θ φ : ℝ) : RyGate φ * RyGate θ ≈ RyGate (θ + φ) := by
  simp only [RyGate, QCircuit.Equiv, QCircuit.eval_seq, QCircuit.eval_gate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    (rw [show ((θ:ℂ) + (φ:ℂ)) / 2 = (θ:ℂ)/2 + (φ:ℂ)/2 by ring]
     simp only [Complex.cos_add, Complex.sin_add]
     ring)

/-- `Rx(φ) · Rx(θ) ≈ Rx(θ+φ)`: X-rotation angles add. -/
theorem rx_plus (θ φ : ℝ) : RxGate φ * RxGate θ ≈ RxGate (θ + φ) := by
  simp only [RxGate, QCircuit.Equiv, QCircuit.eval_seq, QCircuit.eval_gate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    (rw [show ((θ:ℂ) + (φ:ℂ)) / 2 = (θ:ℂ)/2 + (φ:ℂ)/2 by ring]
     simp only [Complex.cos_add, Complex.sin_add]
     ring_nf) <;>
    simp [Complex.I_sq] <;>
    ring_nf

/-- `Ry(0) ≈ 1`. -/
theorem ry_zero : RyGate 0 ≈ (1 : QCircuit 1) := by
  simp only [RyGate, QCircuit.Equiv, QCircuit.eval_gate, QCircuit.eval_id]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `Rx(0) ≈ 1`. -/
theorem rx_zero : RxGate 0 ≈ (1 : QCircuit 1) := by
  simp only [RxGate, QCircuit.Equiv, QCircuit.eval_gate, QCircuit.eval_id]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `Rz(0) ≈ 1`. -/
theorem rz_zero : RzGate 0 ≈ (1 : QCircuit 1) := by
  simp only [RzGate, QCircuit.Equiv, QCircuit.eval_gate, QCircuit.eval_id]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz, Matrix.cons_val_zero, Matrix.cons_val_one]

-- ── X-conjugation flips the rotation angle (N&C Ex 4.7; Fenner Ex 13.2 hint) ──

/-- `X · Ry(θ) · X ≈ Ry(−θ)`. -/
theorem x_ry_x (θ : ℝ) : XGate * RyGate θ * XGate ≈ RyGate (-θ) := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, XGate_bit0, RyGate_bit1,
         QCircuit.apply_add, QCircuit.apply_smul, QCircuit.apply_smul,
         XGate_bit0, XGate_bit1, RyGate_bit0, QState.add_comm,
         QState.smul_scalar_congr (show (-(Real.sin (θ/2) : ℂ))
            = (Real.sin (-θ/2) : ℂ) by
          rw [show -θ/2 = -(θ/2) by ring, Real.sin_neg]; push_cast; ring),
         QState.smul_scalar_congr (show ((Real.cos (θ/2) : ℂ))
            = (Real.cos (-θ/2) : ℂ) by
          rw [show -θ/2 = -(θ/2) by ring, Real.cos_neg])]
  · grw [QCircuit.seq_action, QCircuit.seq_action, XGate_bit1, RyGate_bit0,
         QCircuit.apply_add, QCircuit.apply_smul, QCircuit.apply_smul,
         XGate_bit0, XGate_bit1, RyGate_bit1, QState.add_comm,
         QState.smul_scalar_congr (show ((Real.sin (θ/2) : ℂ))
            = -(Real.sin (-θ/2) : ℂ) by
          rw [show -θ/2 = -(θ/2) by ring, Real.sin_neg]; push_cast; ring),
         QState.smul_scalar_congr (show ((Real.cos (θ/2) : ℂ))
            = (Real.cos (-θ/2) : ℂ) by
          rw [show -θ/2 = -(θ/2) by ring, Real.cos_neg])]

/-- `X · Rz(θ) · X ≈ Rz(−θ)`. -/
theorem x_rz_x (θ : ℝ) : XGate * RzGate θ * XGate ≈ RzGate (-θ) := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, XGate_bit0, RzGate_basis,
         QCircuit.apply_smul, XGate_bit1, RzGate_basis]
    exact QState.smul_scalar_congr (by congr 1; norm_num) _
  · grw [QCircuit.seq_action, QCircuit.seq_action, XGate_bit1, RzGate_basis,
         QCircuit.apply_smul, XGate_bit0, RzGate_basis]
    exact QState.smul_scalar_congr (by congr 1; norm_num) _

-- ── The Z-family as rotations up to global phase (N&C Ex 4.3 and p. 174) ──────

-- Scalar helpers: recognize a constant as a product of two exponentials by summing
-- the arguments. The argument equations (`by norm_num <;> ring`) absorb the `Fin.val`
-- casts the basis-phase lemmas produce.

private lemma one_eq_exp_mul {a b : ℂ} (h : a + b = 0) :
    (1 : ℂ) = Complex.exp a * Complex.exp b := by
  rw [← Complex.exp_add, h, Complex.exp_zero]

private lemma neg_one_eq_exp_mul {a b : ℂ} (h : a + b = (Real.pi : ℂ) * Complex.I) :
    (-1 : ℂ) = Complex.exp a * Complex.exp b := by
  rw [← Complex.exp_add, h, Complex.exp_pi_mul_I]

private lemma I_eq_exp_mul {a b : ℂ}
    (h : a + b = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) :
    Complex.I = Complex.exp a * Complex.exp b := by
  rw [← Complex.exp_add, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

private lemma exp_eq_exp_mul {c a b : ℂ} (h : a + b = c) :
    Complex.exp c = Complex.exp a * Complex.exp b := by
  rw [← Complex.exp_add, h]

/-- `Z ≈ₚ Rz(π)`: `Z = e^{iπ/2} Rz(π)`. -/
theorem z_phase_rz : QCircuit.PhaseEquiv ZGate (RzGate Real.pi) := by
  refine QCircuit.PhaseEquiv.of_basis (Real.pi / 2) fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [ZGate_bit0, RzGate_basis, QState.smul_smul]
    exact (QState.one_smul _).symm.trans
      (QState.smul_scalar_congr (one_eq_exp_mul (by norm_num <;> ring)) _)
  · grw [ZGate_bit1, RzGate_basis, QState.smul_smul]
    exact QState.smul_scalar_congr (neg_one_eq_exp_mul (by norm_num <;> ring)) _

/-- `S ≈ₚ Rz(π/2)`: `S = e^{iπ/4} Rz(π/2)`. -/
theorem s_phase_rz : QCircuit.PhaseEquiv SGate (RzGate (Real.pi / 2)) := by
  refine QCircuit.PhaseEquiv.of_basis (Real.pi / 4) fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [SGate_bit0, RzGate_basis, QState.smul_smul]
    exact (QState.one_smul _).symm.trans
      (QState.smul_scalar_congr (one_eq_exp_mul (by norm_num <;> ring)) _)
  · grw [SGate_bit1, RzGate_basis, QState.smul_smul]
    exact QState.smul_scalar_congr (I_eq_exp_mul (by norm_num <;> ring)) _

/-- `T ≈ₚ Rz(π/4)`: `T = e^{iπ/8} Rz(π/4)` (N&C Ex 4.3). -/
theorem t_phase_rz : QCircuit.PhaseEquiv TGate (RzGate (Real.pi / 4)) := by
  refine QCircuit.PhaseEquiv.of_basis (Real.pi / 8) fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [TGate_bit0, RzGate_basis, QState.smul_smul]
    exact (QState.one_smul _).symm.trans
      (QState.smul_scalar_congr (one_eq_exp_mul (by norm_num <;> ring)) _)
  · grw [TGate_bit1, RzGate_basis, QState.smul_smul]
    exact QState.smul_scalar_congr (exp_eq_exp_mul (by norm_num <;> ring)) _

end

end QLean.Examples
