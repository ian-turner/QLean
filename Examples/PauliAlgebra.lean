import QLean

/-!
# Pauli algebra identities

The single-qubit Pauli relations, proved in the `QState` syntax layer: each identity is
reduced to basis-ket actions with `QCircuit.Equiv.basis_iff_state` and closed by `grw`
chains over the gate-action atoms of `Gate/StateActions.lean`. Scalar bookkeeping ends in
`QState.smul_scalar_congr` with a numeric ℂ-fact; only `h_mul_h` — where the two Hadamard
branches interfere — needs a vector-level collection step.

Sources: Nielsen & Chuang, Exercises 2.41–2.43 (p. 78);
Fenner, CSCE 790 notes §8 (p. 40) and §29.1 (p. 192).

Identities whose right-hand side carries a scalar (`XY = iZ`, `Y = iXZ`, `H = (X+Z)/√2`)
are stated in basis-action form — `QCircuit` has no scalar multiplication — plus a
circuit-level `≈ₚ` (global-phase) corollary where that is the natural reading.
-/

open scoped QLean.Notation

-- The vector-level collection leaves use `fin_cases r <;> fin_cases c <;> simp …`,
-- which trips this purely stylistic linter (`fin_cases c` yields a single goal).
set_option linter.unnecessarySeqFocus false

namespace QLean.Examples

open QLean

noncomputable section

-- ── Involutions: X² = Y² = Z² = H² = 1 ────────────────────────────────────────

/-- `X * X ≈ 1` (N&C Ex 2.41): X is an involution. -/
theorem x_mul_x : XGate * XGate ≈ (1 : QCircuit 1) := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, XGate_bit0, XGate_bit1, QCircuit.id_action]
  · grw [QCircuit.seq_action, XGate_bit1, XGate_bit0, QCircuit.id_action]

/-- `Z * Z ≈ 1`: Z is an involution. -/
theorem z_mul_z : ZGate * ZGate ≈ (1 : QCircuit 1) := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, ZGate_bit0, ZGate_bit0, QCircuit.id_action]
  · grw [QCircuit.seq_action, ZGate_bit1, QCircuit.apply_smul, ZGate_bit1,
         QState.smul_smul, QCircuit.id_action,
         QState.smul_scalar_congr (show (-1 : ℂ) * -1 = 1 by norm_num), QState.one_smul]

/-- `Y * Y ≈ 1`: Y is an involution. -/
theorem y_mul_y : YGate * YGate ≈ (1 : QCircuit 1) := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, YGate_bit0, QCircuit.apply_smul, YGate_bit1,
         QState.smul_smul, QCircuit.id_action,
         QState.smul_scalar_congr (show Complex.I * -Complex.I = 1 by
           rw [mul_neg, Complex.I_mul_I]; norm_num),
         QState.one_smul]
  · grw [QCircuit.seq_action, YGate_bit1, QCircuit.apply_smul, YGate_bit0,
         QState.smul_smul, QCircuit.id_action,
         QState.smul_scalar_congr (show -Complex.I * Complex.I = 1 by
           rw [neg_mul, Complex.I_mul_I]; norm_num),
         QState.one_smul]

/-- `H * H ≈ 1` (N&C p. 174): H is an involution. The two Hadamard branches interfere,
    so after the `grw` chain the like-ket terms are collected at the vector level —
    the irreducible arithmetic leaf of this identity. -/
theorem h_mul_h : HGate * HGate ≈ (1 : QCircuit 1) := by
  refine (QCircuit.Equiv.basis_iff_state _ _).mpr fun i => ?_
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, HGate_bit0, QCircuit.apply_smul, QCircuit.apply_add,
         HGate_bit0, HGate_bit1, QCircuit.id_action]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; simp [inv_pow, sqrt2_sq_cast])
  · grw [QCircuit.seq_action, HGate_bit1, QCircuit.apply_smul, QCircuit.apply_add,
         QCircuit.apply_smul, HGate_bit0, HGate_bit1, QCircuit.id_action]
    simp only [QState.Equiv, QState.eval_smul, QState.eval_add, QState.eval_basis]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [ket_apply, Matrix.smul_apply, Matrix.add_apply] <;>
      (ring_nf; simp [inv_pow, sqrt2_sq_cast])

-- ── Pauli products: XY = iZ, YZ = iX, ZX = iY (N&C Ex 2.43) ───────────────────
-- `QCircuit` has no scalar action, so the exact-phase forms are stated on basis kets;
-- a circuit-level global-phase form (`≈ₚ`, γ = π/2) follows via `PhaseEquiv.of_basis`.

/-- `XY = iZ` in basis-action form. -/
theorem xy_basis (a : Fin (2^1)) :
    (XGate * YGate) * ❘a⟩ ≈ Complex.I • (ZGate * ❘a⟩) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, YGate_bit0, QCircuit.apply_smul, XGate_bit1, ZGate_bit0]
  · grw [QCircuit.seq_action, YGate_bit1, QCircuit.apply_smul, XGate_bit0, ZGate_bit1,
         QState.smul_smul,
         QState.smul_scalar_congr (show -Complex.I = Complex.I * (-1 : ℂ) by ring)]

/-- `YZ = iX` in basis-action form. -/
theorem yz_basis (a : Fin (2^1)) :
    (YGate * ZGate) * ❘a⟩ ≈ Complex.I • (XGate * ❘a⟩) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, ZGate_bit0, YGate_bit0, XGate_bit0]
  · grw [QCircuit.seq_action, ZGate_bit1, QCircuit.apply_smul, YGate_bit1,
         QState.smul_smul, XGate_bit1,
         QState.smul_scalar_congr (show (-1 : ℂ) * -Complex.I = Complex.I by ring)]

/-- `ZX = iY` in basis-action form. -/
theorem zx_basis (a : Fin (2^1)) :
    (ZGate * XGate) * ❘a⟩ ≈ Complex.I • (YGate * ❘a⟩) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, XGate_bit0, ZGate_bit1, YGate_bit0, QState.smul_smul,
         QState.smul_scalar_congr (show (-1 : ℂ) = Complex.I * Complex.I from
           Complex.I_mul_I.symm)]
  · grw [QCircuit.seq_action, XGate_bit1, ZGate_bit0, YGate_bit1, QState.smul_smul,
         QState.smul_scalar_congr (show Complex.I * -Complex.I = 1 by
           rw [mul_neg, Complex.I_mul_I]; norm_num),
         QState.one_smul]

/-- `XY ≈ₚ Z`: the circuit-level reading of `XY = iZ`, up to the global phase
    `i = e^{iπ/2}`. -/
theorem xy_phase_z : QCircuit.PhaseEquiv (XGate * YGate) ZGate := by
  refine QCircuit.PhaseEquiv.of_basis (Real.pi / 2) fun i => ?_
  rw [show Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) = Complex.I by
    rw [Complex.exp_mul_I]; push_cast; simp]
  exact xy_basis i

/-- `XY = −YX` (anticommutation, N&C Ex 2.41) in basis-action form. -/
theorem xy_anticomm (a : Fin (2^1)) :
    (XGate * YGate) * ❘a⟩ ≈ (-1 : ℂ) • ((YGate * XGate) * ❘a⟩) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, YGate_bit0, QCircuit.apply_smul, XGate_bit1,
         QCircuit.seq_action, XGate_bit0, YGate_bit1, QState.smul_smul,
         QState.smul_scalar_congr (show Complex.I = (-1 : ℂ) * -Complex.I by ring)]
  · grw [QCircuit.seq_action, YGate_bit1, QCircuit.apply_smul, XGate_bit0,
         QCircuit.seq_action, XGate_bit1, YGate_bit0, QState.smul_smul,
         QState.smul_scalar_congr (show -Complex.I = (-1 : ℂ) * Complex.I by ring)]

/-- `Y = iXZ` (Fenner §29.1) in basis-action form. -/
theorem y_eq_i_xz (a : Fin (2^1)) :
    YGate * ❘a⟩ ≈ Complex.I • ((XGate * ZGate) * ❘a⟩) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [YGate_bit0, QCircuit.seq_action, ZGate_bit0, XGate_bit0]
  · grw [YGate_bit1, QCircuit.seq_action, ZGate_bit1, QCircuit.apply_smul, XGate_bit1,
         QState.smul_smul,
         QState.smul_scalar_congr (show -Complex.I = Complex.I * (-1 : ℂ) by ring)]

/-- `H = (X + Z)/√2` (N&C p. 174) in basis-action form: `QCircuit` has no sum of
    circuits, so the right-hand side is a superposition of the two actions. -/
theorem h_eq_x_add_z (a : Fin (2^1)) :
    HGate * ❘a⟩ ≈ ((Real.sqrt 2)⁻¹ : ℂ) • (XGate * ❘a⟩ + ZGate * ❘a⟩) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [HGate_bit0, XGate_bit0, ZGate_bit0, QState.add_comm]
  · grw [HGate_bit1, XGate_bit1, ZGate_bit1]

end

end QLean.Examples
