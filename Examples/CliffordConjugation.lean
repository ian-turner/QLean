import QLean
import Examples.PauliAlgebra

/-!
# Clifford conjugation and phase-gate identities

The Hadamard conjugation table `HXH = Z`, `HZH = X`, `HYH = −Y` (N&C Exercise 4.13,
"circuit identities", p. 177) and the phase-gate ladder `T² = S`, `S² = Z`, `T⁸ = 1`,
`X = HS²H` (N&C p. 197; Fenner §11 p. 70, Ex 29.22 p. 191).

Proof style: basis reduction + `grw` over the gate-action atoms. The composite results
(`T⁸ = 1`, `X = HS²H`) are then proved *purely at the circuit level* by `grw`-rewriting
sub-circuits with the earlier equivalences — no basis kets at all — showing the `≈`
congruence machinery doing equational reasoning on circuits.
-/

open scoped QLean.Notation

-- The vector-level collection leaves use `fin_cases r <;> fin_cases c <;> simp …`,
-- which trips this purely stylistic linter (`fin_cases c` yields a single goal).
set_option linter.unnecessarySeqFocus false

namespace QLean.Examples

open QLean

noncomputable section

-- ── Hadamard conjugation of the Paulis (N&C Ex 4.13) ──────────────────────────

/-- `HXH ≈ Z`. -/
theorem hxh : HGate * XGate * HGate ≈ ZGate := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, HGate_bit0, QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.seq_action, QCircuit.seq_action, XGate_bit0, XGate_bit1,
         HGate_bit1, HGate_bit0, ZGate_bit0]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; simp [inv_pow, sqrt2_sq_cast])
  · grw [QCircuit.seq_action, HGate_bit1, QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.apply_smul, QCircuit.seq_action, QCircuit.seq_action,
         XGate_bit0, XGate_bit1, HGate_bit1, HGate_bit0, ZGate_bit1]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; simp [inv_pow, sqrt2_sq_cast])

/-- `HZH ≈ X`. -/
theorem hzh : HGate * ZGate * HGate ≈ XGate := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, HGate_bit0, QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.seq_action, QCircuit.seq_action, ZGate_bit0, ZGate_bit1,
         QCircuit.apply_smul, HGate_bit0, HGate_bit1, XGate_bit0]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; simp [inv_pow, sqrt2_sq_cast])
  · grw [QCircuit.seq_action, HGate_bit1, QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.apply_smul, QCircuit.seq_action, QCircuit.seq_action,
         ZGate_bit0, ZGate_bit1, QCircuit.apply_smul, HGate_bit0, HGate_bit1, XGate_bit1]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; simp [inv_pow, sqrt2_sq_cast])

/-- `HYH = −Y` in basis-action form (the sign makes a strict circuit equivalence
    impossible). -/
theorem hyh_basis (a : Fin (2^1)) :
    (HGate * YGate * HGate) * ❘a⟩ ≈ (-1 : ℂ) • (YGate * ❘a⟩) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, HGate_bit0, QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.seq_action, QCircuit.seq_action, YGate_bit0, YGate_bit1,
         QCircuit.apply_smul, QCircuit.apply_smul, HGate_bit1, HGate_bit0]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; norm_num [inv_pow, sqrt2_sq_cast]) <;> ring
  · grw [QCircuit.seq_action, HGate_bit1, QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.apply_smul, QCircuit.seq_action, QCircuit.seq_action,
         YGate_bit0, YGate_bit1, QCircuit.apply_smul, QCircuit.apply_smul,
         HGate_bit1, HGate_bit0]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; norm_num [inv_pow, sqrt2_sq_cast]) <;> ring

/-- `HYH ≈ₚ Y`: circuit-level reading of `HYH = −Y`, up to the global phase `−1 = e^{iπ}`. -/
theorem hyh_phase_y : QCircuit.PhaseEquiv (HGate * YGate * HGate) YGate := by
  refine QCircuit.PhaseEquiv.of_basis Real.pi fun i => ?_
  rw [show Complex.exp ((Real.pi : ℝ) * Complex.I) = -1 from Complex.exp_pi_mul_I]
  exact hyh_basis i

-- ── The phase-gate ladder: T² = S, S² = Z, T⁸ = 1 ─────────────────────────────

/-- `T * T ≈ S` (N&C p. 174: T is "the square root of S"). -/
theorem t_mul_t : TGate * TGate ≈ SGate := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, TGate_bit0, TGate_bit0, SGate_bit0]
  · grw [QCircuit.seq_action, TGate_bit1, QCircuit.apply_smul, TGate_bit1,
         QState.smul_smul, SGate_bit1,
         QState.smul_scalar_congr (show Complex.exp (Complex.I * Real.pi / 4) *
             Complex.exp (Complex.I * Real.pi / 4) = Complex.I by
           rw [← Complex.exp_add,
               show Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
                  = (Real.pi / 2 : ℝ) * Complex.I by push_cast; ring,
               Complex.exp_mul_I]
           push_cast; simp)]

/-- `S * S ≈ Z` (N&C p. 197, used in the H+T universality construction). -/
theorem s_mul_s : SGate * SGate ≈ ZGate := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, SGate_bit0, SGate_bit0, ZGate_bit0]
  · grw [QCircuit.seq_action, SGate_bit1, QCircuit.apply_smul, SGate_bit1,
         QState.smul_smul, ZGate_bit1,
         QState.smul_scalar_congr Complex.I_mul_I]

/-- `T⁸ ≈ 1` (Fenner Ex 13.2(3)): proved purely at the circuit level by rewriting
    sub-circuits — `T² ≈ S` four times, `S² ≈ Z` twice, `Z² ≈ 1` once — with no basis
    kets in sight. -/
theorem t_pow_8 :
    ((TGate * TGate) * (TGate * TGate)) * ((TGate * TGate) * (TGate * TGate))
      ≈ (1 : QCircuit 1) := by
  grw [t_mul_t, s_mul_s, z_mul_z]

/-- `X ≈ H S² H` (Fenner Ex 29.22(2)): X from `{H, S}` alone, again purely at the
    circuit level via `S² ≈ Z` and `HZH ≈ X`. -/
theorem x_eq_h_ss_h : HGate * (SGate * SGate) * HGate ≈ XGate := by
  grw [s_mul_s]
  exact hzh

end

end QLean.Examples
