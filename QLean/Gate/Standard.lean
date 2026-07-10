import QLean.Basic.Hilbert
import QLean.Circuit.Semantics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.IsDiag

open scoped Matrix

-- Close a concrete `IsUnitary M` goal after `unfold IsUnitary M`.
-- Including sum_univ_two/four/eight together is harmless: the wrong ones won't fire.
macro "prove_unitary" : tactic =>
  `(tactic| ext i j <;> fin_cases i <;> fin_cases j
        <;> simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
                Fin.sum_univ_four, Fin.sum_univ_eight,
                Matrix.cons_val_zero, Matrix.cons_val_one])

noncomputable section

namespace QLean

-- (Real.sqrt 2 : ℂ)^2 = 2; prerequisite for H unitarity and for every identity with
-- H factors on both sides. Public: the `circuit_eq` closer below and the example files
-- need it to discharge leftover √2 arithmetic.
lemma sqrt2_sq_cast : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  norm_cast

lemma sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

-- exp(z) * conj(exp(z)) = 1 when z + conj(z) = 0 (z purely imaginary)
private lemma exp_mul_conj_eq_one {z : ℂ} (h : z + starRingEnd ℂ z = 0) :
    Complex.exp z * starRingEnd ℂ (Complex.exp z) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add, h, Complex.exp_zero]

private lemma two_coe_complex : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast

-- ── Single-qubit gates ────────────────────────────────────────────────────────

/-- Hadamard gate: maps |0⟩ to (|0⟩+|1⟩)/√2, creating uniform superposition. -/
def H : QMatrix 1 :=
  !![(Real.sqrt 2 : ℂ)⁻¹,  (Real.sqrt 2 : ℂ)⁻¹;
     (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- Pauli-X (bit flip): swaps |0⟩ and |1⟩. -/
def X : QMatrix 1 := !![0, 1; 1, 0]

/-- Pauli-Y. -/
def Y : QMatrix 1 := !![0, -Complex.I; Complex.I, 0]

/-- Pauli-Z (phase flip): |1⟩ ↦ -|1⟩. -/
def Z : QMatrix 1 := !![1, 0; 0, -1]

/-- S gate: diagonal phase gate, π/2 rotation around Z. -/
def S : QMatrix 1 := !![1, 0; 0, Complex.I]

/-- T gate: diagonal phase gate, π/4 rotation around Z. -/
def T : QMatrix 1 := !![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)]

/-- T† (T-dagger): the adjoint of `T`, `diag(1, e^{-iπ/4})`. A first-class gate because
    the standard Toffoli and controlled-S decompositions use it directly. -/
def Tdg : QMatrix 1 := !![1, 0; 0, Complex.exp (-(Complex.I * Real.pi / 4))]

/-- Z-rotation by angle `θ`: diagonal with eigenphases ∓θ/2 on |0⟩, |1⟩. -/
noncomputable def Rz (θ : ℝ) : QMatrix 1 :=
  !![Complex.exp (-Complex.I * θ / 2), 0;
     0, Complex.exp (Complex.I * θ / 2)]

/-- X-rotation by angle `θ`. -/
noncomputable def Rx (θ : ℝ) : QMatrix 1 :=
  let c : ℂ := Real.cos (θ / 2)
  let s : ℂ := Real.sin (θ / 2)
  !![c, -Complex.I * s; -Complex.I * s, c]

/-- Y-rotation by angle `θ`. -/
noncomputable def Ry (θ : ℝ) : QMatrix 1 :=
  let c : ℂ := Real.cos (θ / 2)
  let s : ℂ := Real.sin (θ / 2)
  !![c, -s; s, c]

/-- Square root of X (the `V` gate of Nielsen & Chuang Figure 4.8): `sqrtX * sqrtX = X`. -/
def sqrtX : QMatrix 1 :=
  !![(1 + Complex.I) / 2, (1 - Complex.I) / 2;
     (1 - Complex.I) / 2, (1 + Complex.I) / 2]

-- ── Two-qubit gates (LSB convention: qubit 0 = low bit) ───────────────────────

/-- CNOT: control = qubit 0 (low bit), target = qubit 1; flips the target when the
    control is set. (LSB convention; the MSB textbook matrix differs.) -/
def CNOT : QMatrix 2 :=
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0]

/-- CZ: phase flip on `|11⟩`. Symmetric, so identical in the LSB and MSB conventions. -/
def CZ : QMatrix 2 :=
  !![1, 0, 0,  0;
     0, 1, 0,  0;
     0, 0, 1,  0;
     0, 0, 0, -1]

/-- SWAP: exchanges qubits 0 and 1. -/
def SWAP : QMatrix 2 :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

/-- Reversed CNOT: control = qubit 1 (high bit), target = qubit 0; flips the low qubit
    when the high qubit is set. The mirror image of `CNOT` under qubit exchange. -/
def CNOTRev : QMatrix 2 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- Square root of SWAP: `sqrtSWAP * sqrtSWAP = SWAP`, fixing `|00⟩` and `|11⟩`.
    Symmetric, so identical in the LSB and MSB conventions. -/
def sqrtSWAP : QMatrix 2 :=
  !![1, 0, 0, 0;
     0, (1 + Complex.I) / 2, (1 - Complex.I) / 2, 0;
     0, (1 - Complex.I) / 2, (1 + Complex.I) / 2, 0;
     0, 0, 0, 1]

/-- Toffoli (CCX): controls = qubits 0,1, target = qubit 2; flips the target when both
    controls are set. In the LSB convention this swaps basis indices `3` (both controls set,
    target clear) and `7` (all set); the MSB textbook matrix differs. -/
def Toffoli : QMatrix 3 :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- CCZ: phase flip on `|111⟩` (index 7). Fully symmetric among its three qubits, so
    identical in the LSB and MSB conventions. -/
def CCZ : QMatrix 3 :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, -1]

/-- Fredkin (controlled-SWAP): control = qubit 0 (low bit), exchanges qubits 1 and 2 when
    the control is set. In the LSB convention this swaps basis indices `3` (`q₀q₁ = 11`)
    and `5` (`q₀q₂ = 11`); the MSB textbook matrix differs. -/
def Fredkin : QMatrix 3 :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

-- ── Controlled-U (2-qubit); ctrl=qubit0, tgt=qubit1 ─────────────────────────

/-- Controlled-`U`: control = qubit 0, target = qubit 1. Applies `U` to the target
    when the control is set, identity otherwise. -/
def controlled (U : QMatrix 1) : QMatrix 2 :=
  !![1,      0,      0,      0;
     0, U 0 0,      0, U 0 1;
     0,      0,      1,      0;
     0, U 1 0,      0, U 1 1]

-- ── Unitarity proofs ──────────────────────────────────────────────────────────

theorem isUnitary_H : IsUnitary H := by
  unfold IsUnitary H
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    (ring_nf; rw [inv_pow, sqrt2_sq_cast]; norm_num)

theorem isUnitary_X    : IsUnitary X    := by unfold IsUnitary X;    prove_unitary
theorem isUnitary_Y    : IsUnitary Y    := by unfold IsUnitary Y;    prove_unitary
theorem isUnitary_Z    : IsUnitary Z    := by unfold IsUnitary Z;    prove_unitary
theorem isUnitary_CNOT : IsUnitary CNOT := by unfold IsUnitary CNOT; prove_unitary
theorem isUnitary_CNOTRev : IsUnitary CNOTRev := by unfold IsUnitary CNOTRev; prove_unitary

theorem isUnitary_Tdg : IsUnitary Tdg := by
  unfold IsUnitary Tdg
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  apply exp_mul_conj_eq_one
  have : -(Complex.I * ↑Real.pi / 4) = Complex.I * ↑(-(Real.pi / 4)) := by push_cast; ring
  rw [this, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
theorem isUnitary_CZ   : IsUnitary CZ   := by unfold IsUnitary CZ;   prove_unitary
theorem isUnitary_SWAP : IsUnitary SWAP := by unfold IsUnitary SWAP; prove_unitary

theorem isUnitary_Toffoli : IsUnitary Toffoli := by unfold IsUnitary Toffoli; prove_unitary

theorem isUnitary_CCZ : IsUnitary CCZ := by unfold IsUnitary CCZ; prove_unitary

theorem isUnitary_Fredkin : IsUnitary Fredkin := by unfold IsUnitary Fredkin; prove_unitary

theorem isUnitary_sqrtX : IsUnitary sqrtX := by
  unfold IsUnitary sqrtX
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_ofNat,
          Complex.conj_I] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring_nf

theorem isUnitary_sqrtSWAP : IsUnitary sqrtSWAP := by
  unfold IsUnitary sqrtSWAP
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_ofNat,
          Complex.conj_I] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring_nf

set_option maxHeartbeats 800000 in
/-- Unitarity of `controlled U` lifted from unitarity of `U`. -/
theorem isUnitary_controlled {U : QMatrix 1} (hu : IsUnitary U) :
    IsUnitary (controlled U) := by
  -- simp converts star to (starRingEnd ℂ) via Complex.star_def; declare h-lemmas to match
  have h00 : U 0 0 * (starRingEnd ℂ) (U 0 0) + U 0 1 * (starRingEnd ℂ) (U 0 1) = 1 := by
    have := congr_fun₂ hu 0 0
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at this
    exact this
  have h01 : U 0 0 * (starRingEnd ℂ) (U 1 0) + U 0 1 * (starRingEnd ℂ) (U 1 1) = 0 := by
    have := congr_fun₂ hu 0 1
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at this
    exact this
  have h10 : U 1 0 * (starRingEnd ℂ) (U 0 0) + U 1 1 * (starRingEnd ℂ) (U 0 1) = 0 := by
    have := congr_fun₂ hu 1 0
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at this
    exact this
  have h11 : U 1 0 * (starRingEnd ℂ) (U 1 0) + U 1 1 * (starRingEnd ℂ) (U 1 1) = 1 := by
    have := congr_fun₂ hu 1 1
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at this
    exact this
  unfold IsUnitary controlled
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
          h00, h01, h10, h11]

theorem isUnitary_S : IsUnitary S := by unfold IsUnitary S; prove_unitary

theorem isUnitary_T : IsUnitary T := by
  unfold IsUnitary T
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  apply exp_mul_conj_eq_one
  have : Complex.I * ↑Real.pi / 4 = Complex.I * ↑(Real.pi / 4) := by push_cast; ring
  rw [this, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

theorem isUnitary_Rz (θ : ℝ) : IsUnitary (Rz θ) := by
  unfold IsUnitary Rz
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  · apply exp_mul_conj_eq_one
    have : -(Complex.I * ↑θ) / 2 = Complex.I * ↑(-θ / 2) := by push_cast; ring
    rw [this, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  · apply exp_mul_conj_eq_one
    have : Complex.I * ↑θ / 2 = Complex.I * ↑(θ / 2) := by push_cast; ring
    rw [this, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

theorem isUnitary_Rx (θ : ℝ) : IsUnitary (Rx θ) := by
  unfold IsUnitary Rx
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.conj_I, map_neg, map_mul]
  all_goals simp only [← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
    map_div₀, two_coe_complex]
  · ring_nf; simp [Complex.I_sq]
  · ring
  · ring
  · ring_nf; simp [Complex.I_sq]

theorem isUnitary_Ry (θ : ℝ) : IsUnitary (Ry θ) := by
  unfold IsUnitary Ry
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals simp only [← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
    map_div₀, two_coe_complex]
  · ring_nf; simp
  · ring
  · ring
  · ring_nf; simp

-- ── QFT phase gate Rₖ ─────────────────────────────────────────────────────────

/-- Phase gate `Rₖ` (Nielsen & Chuang §5.1): diagonal `diag(1, e^{2πi/2ᵏ})`, the rotation
    family of the quantum Fourier transform. Note `R₁ = Z`, `R₂ = S`, `R₃ = T`. -/
noncomputable def Rk (k : ℕ) : QMatrix 1 :=
  !![1, 0;
     0, Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ k)]

/-- `Rₖ` is diagonal. -/
theorem Rk_isDiag (k : ℕ) : Matrix.IsDiag (Rk k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [Rk, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem isUnitary_Rk (k : ℕ) : IsUnitary (Rk k) := by
  unfold IsUnitary Rk
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  apply exp_mul_conj_eq_one
  simp only [map_div₀, map_mul, map_pow, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- A controlled diagonal gate is diagonal: the only off-diagonal candidates `(1,3)` and `(3,1)`
    carry `U 0 1` and `U 1 0`, which vanish when `U` is diagonal. -/
theorem controlled_isDiag {U : QMatrix 1} (hU : Matrix.IsDiag U) :
    Matrix.IsDiag (controlled U) := by
  have h01 : U 0 1 = 0 := hU (by decide)
  have h10 : U 1 0 = 0 := hU (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [controlled, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The diagonal eigenphase of `controlled (Rk k)`: the rotation phase `e^{2πi/2ᵏ}` on the `|11⟩`
    index (`3`), and `1` on every other diagonal entry. The single matrix-entry fact behind an
    embedded controlled-rotation layer (used by `embed_controlled_Rk_action`). -/
theorem controlled_Rk_diag (k : ℕ) (idx : Fin (2 ^ 2)) :
    (controlled (Rk k)) idx idx
      = if idx = 3 then Complex.exp (2 * Real.pi * Complex.I / (2:ℂ) ^ k) else 1 := by
  fin_cases idx <;> simp [controlled, Rk, Matrix.cons_val_zero, Matrix.cons_val_one]

-- ── Gate actions on computational basis states ────────────────────────────────

theorem Rz_ket_zero (θ : ℝ) : Rz θ * ket 0 = Complex.exp (-Complex.I * θ / 2) • ket 0 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Rz, ket_apply, Matrix.mul_apply, Matrix.smul_apply]

theorem Rz_ket_one (θ : ℝ) : Rz θ * ket 1 = Complex.exp (Complex.I * θ / 2) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Rz, ket_apply, Matrix.mul_apply, Matrix.smul_apply]

-- Compute tensorIndexEquiv 1 1 ⟨a, b⟩ using the known symm lemmas.
-- In the (1,1) case, the index is a.val + b.val * 2 (a occupies the low bit).
private lemma te11_of_symm (a b : Fin 2) (n : Fin 4)
    (h1 : n.val % 2 = a.val) (h2 : n.val / 2 = b.val) :
    tensorIndexEquiv 1 1 ⟨a, b⟩ = n := by
  have hsymm : (tensorIndexEquiv 1 1).symm n = ⟨a, b⟩ := Prod.ext
    (Fin.ext (by rw [tensorIndexEquiv_symm_fst_val]; simp [pow_one, h1]))
    (Fin.ext (by rw [tensorIndexEquiv_symm_snd_val]; simp [pow_one, h2]))
  calc tensorIndexEquiv 1 1 ⟨a, b⟩
      = tensorIndexEquiv 1 1 ((tensorIndexEquiv 1 1).symm n) := by rw [hsymm]
    _ = n := (tensorIndexEquiv 1 1).apply_symm_apply n

private lemma te11_00 : tensorIndexEquiv 1 1 ⟨(0:Fin 2), (0:Fin 2)⟩ = (0:Fin 4) :=
  te11_of_symm _ _ _ (by norm_num) (by norm_num)
private lemma te11_10 : tensorIndexEquiv 1 1 ⟨(1:Fin 2), (0:Fin 2)⟩ = (1:Fin 4) :=
  te11_of_symm _ _ _ (by norm_num) (by norm_num)
private lemma te11_01 : tensorIndexEquiv 1 1 ⟨(0:Fin 2), (1:Fin 2)⟩ = (2:Fin 4) :=
  te11_of_symm _ _ _ (by norm_num) (by norm_num)
private lemma te11_11 : tensorIndexEquiv 1 1 ⟨(1:Fin 2), (1:Fin 2)⟩ = (3:Fin 4) :=
  te11_of_symm _ _ _ (by norm_num) (by norm_num)

-- Four concrete actions of CNOT on computational basis states (in Fin 4 index form).
-- Uses the same simp set as prove_unitary: Matrix.cons_val_zero/one handle !![...] indexing.
private lemma CNOT_ket_0_eq_0 : CNOT * ket (0:Fin 4) = ket 0 := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  fin_cases r <;>
  simp [Matrix.mul_apply, CNOT, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma CNOT_ket_1_eq_3 : CNOT * ket (1:Fin 4) = ket 3 := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  fin_cases r <;>
  simp [Matrix.mul_apply, CNOT, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma CNOT_ket_2_eq_2 : CNOT * ket (2:Fin 4) = ket 2 := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  fin_cases r <;>
  simp [Matrix.mul_apply, CNOT, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma CNOT_ket_3_eq_1 : CNOT * ket (3:Fin 4) = ket 1 := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  fin_cases r <;>
  simp [Matrix.mul_apply, CNOT, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- CNOT maps `|a, b⟩` to `|a, a+b⟩` (control preserved, target XORed with control). -/
theorem CNOT_ket_pair (a b : Fin 2) :
    CNOT * ket (tensorIndexEquiv 1 1 ⟨a, b⟩) = ket (tensorIndexEquiv 1 1 ⟨a, a + b⟩) := by
  have ha : a = 0 ∨ a = 1 := by omega
  have hb : b = 0 ∨ b = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [te11_00, show (0:Fin 2) + 0 = 0 from by decide, te11_00]; exact CNOT_ket_0_eq_0
  · rw [te11_01, show (0:Fin 2) + 1 = 1 from by decide, te11_01]; exact CNOT_ket_2_eq_2
  · rw [te11_10, show (1:Fin 2) + 0 = 1 from by decide, te11_11]; exact CNOT_ket_1_eq_3
  · rw [te11_11, show (1:Fin 2) + 1 = 0 from by decide, te11_10]; exact CNOT_ket_3_eq_1

theorem Rz_ket_diag (θ : ℝ) (a : Fin 2) : Rz θ * ket a = Rz θ a a • ket a := by
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl
  · rw [Rz_ket_zero]; simp [Rz, Matrix.cons_val_zero]
  · rw [Rz_ket_one]; simp [Rz, Matrix.cons_val_one]

-- ── Single-qubit basis-state actions ──────────────────────────────────────────

theorem X_ket_zero : X * ket (0 : Fin 2) = ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [X, ket_apply, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem X_ket_one : X * ket (1 : Fin 2) = ket 0 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [X, ket_apply, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Y_ket_zero : Y * ket (0 : Fin 2) = Complex.I • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Y, ket_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Y_ket_one : Y * ket (1 : Fin 2) = (-Complex.I) • ket 0 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Y, ket_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Z_ket_zero : Z * ket (0 : Fin 2) = ket 0 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Z, ket_apply, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Z_ket_one : Z * ket (1 : Fin 2) = (-1 : ℂ) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Z, ket_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem S_ket_zero : S * ket (0 : Fin 2) = ket 0 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [S, ket_apply, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem S_ket_one : S * ket (1 : Fin 2) = Complex.I • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [S, ket_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem H_ket_zero : H * ket (0 : Fin 2) = (Real.sqrt 2)⁻¹ • (ket 0 + ket 1) := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [H, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem H_ket_one : H * ket (1 : Fin 2) = (Real.sqrt 2)⁻¹ • (ket 0 + (-1 : ℂ) • ket 1) := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [H, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

-- Phase-form matrix entries of `H`: both rows have constant magnitude `(√2)⁻¹`, with row `1`
-- carrying the sign `(-1)^t = e^{2πi·t/2}`. These two entry facts are the only matrix-level input
-- to the embedded-Hadamard state action `embed_H_action`.

theorem H_row0 (t : Fin (2 ^ 1)) : (H : QMatrix 1) 0 t = (Real.sqrt 2 : ℂ)⁻¹ := by
  fin_cases t <;> simp [H, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem H_row1 (t : Fin (2 ^ 1)) :
    (H : QMatrix 1) 1 t = (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / 2) := by
  fin_cases t
  · simp [H, Matrix.cons_val_zero, Matrix.cons_val_one]
  · show (H : QMatrix 1) 1 1
        = (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((1 : Fin (2 ^ 1)).val : ℂ) / 2)
    rw [show (2 * (Real.pi:ℂ) * Complex.I * ((1 : Fin (2 ^ 1)).val : ℂ)) / 2 = (Real.pi:ℂ) * Complex.I from by
          simp only [Fin.val_one, Nat.cast_one]; ring, Complex.exp_pi_mul_I]
    simp [H, Matrix.cons_val_one]

-- ── Further single-qubit basis-state actions ──────────────────────────────────

theorem T_ket_zero : T * ket (0 : Fin 2) = ket 0 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [T, ket_apply, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem T_ket_one :
    T * ket (1 : Fin 2) = Complex.exp (Complex.I * Real.pi / 4) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [T, ket_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem sqrtX_ket_zero :
    sqrtX * ket (0 : Fin 2) = ((1 + Complex.I) / 2) • ket 0 + ((1 - Complex.I) / 2) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [sqrtX, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem sqrtX_ket_one :
    sqrtX * ket (1 : Fin 2) = ((1 - Complex.I) / 2) • ket 0 + ((1 + Complex.I) / 2) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [sqrtX, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Ry_ket_zero (θ : ℝ) :
    Ry θ * ket (0 : Fin 2)
      = (Real.cos (θ/2) : ℂ) • ket 0 + (Real.sin (θ/2) : ℂ) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Ry, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Ry_ket_one (θ : ℝ) :
    Ry θ * ket (1 : Fin 2)
      = (-(Real.sin (θ/2) : ℂ)) • ket 0 + (Real.cos (θ/2) : ℂ) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Ry, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Rx_ket_zero (θ : ℝ) :
    Rx θ * ket (0 : Fin 2)
      = (Real.cos (θ/2) : ℂ) • ket 0 + (-Complex.I * Real.sin (θ/2)) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Rx, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Rx_ket_one (θ : ℝ) :
    Rx θ * ket (1 : Fin 2)
      = (-Complex.I * Real.sin (θ/2)) • ket 0 + (Real.cos (θ/2) : ℂ) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Rx, ket_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Basis expansion of an arbitrary 1-qubit vector: the bridge from basis-pair actions to
    arbitrary-vector actions (`controlled_tensorState_*` below). -/
theorem qvector1_expand (v : QVector 1) : v = v 0 0 • ket 0 + v 1 0 • ket 1 := by
  ext r s; obtain rfl : s = 0 := Subsingleton.elim s 0
  fin_cases r <;>
  simp [ket_apply, Matrix.smul_apply, Matrix.add_apply]

-- ── Two-qubit gate actions on tensor states ───────────────────────────────────
-- Control-split lemmas: `controlled U` (and its instances CNOT = controlled X,
-- CZ = controlled Z) acts on `|0⟩ ⊗ v` as the identity and on `|1⟩ ⊗ v` as `U` on the
-- target factor. Stated for an arbitrary target vector so the state layer can rewrite
-- without decomposing the target into basis kets. LSB convention: the control (qubit 0)
-- is the LOW factor of `tensorState`.

/-- CNOT is `controlled X` (control = qubit 0, target = qubit 1). -/
theorem CNOT_eq_controlled_X : CNOT = controlled X := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CNOT, controlled, X, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- CZ is `controlled Z`. -/
theorem CZ_eq_controlled_Z : CZ = controlled Z := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CZ, controlled, Z, Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma controlled_ket_pair_zero (U : QMatrix 1) (b : Fin 2) :
    controlled U * ket (tensorIndexEquiv 1 1 ⟨0, b⟩) = ket (tensorIndexEquiv 1 1 ⟨0, b⟩) := by
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl <;>
    [rw [te11_00]; rw [te11_01]] <;>
    (ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
     rw [mul_ket_apply]
     fin_cases r <;>
       simp [controlled, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one])

private lemma controlled_ket_pair_one (U : QMatrix 1) (b : Fin 2) :
    controlled U * ket (tensorIndexEquiv 1 1 ⟨1, b⟩)
      = tensorState (ket 1) (U * ket b) := by
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl <;>
    [rw [te11_10]; rw [te11_11]] <;>
    (ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
     rw [mul_ket_apply]
     have t111 : (tensorIndexEquiv 1 1).symm 1 = (1, 0) := by decide
     have t113 : (tensorIndexEquiv 1 1).symm 3 = (1, 1) := by decide
     fin_cases r <;>
       simp [controlled, ket_apply, tensorState_apply, mul_ket_apply, t111, t113,
             (by decide : (tensorIndexEquiv 1 1).symm 0 = (0, 0)),
             (by decide : (tensorIndexEquiv 1 1).symm 2 = (0, 1)),
             Matrix.cons_val_zero, Matrix.cons_val_one])

/-- `controlled U` fixes any product state whose control qubit is `|0⟩`. -/
theorem controlled_tensorState_zero (U : QMatrix 1) (v : QVector 1) :
    controlled U * tensorState (ket 0) v = tensorState (ket 0) v := by
  rw [qvector1_expand v]
  simp only [tensorState_add_right, tensorState_smul_right, Matrix.mul_add, Matrix.mul_smul,
             ket_tensorState]
  rw [controlled_ket_pair_zero, controlled_ket_pair_zero]

/-- `controlled U` applies `U` to the target factor when the control qubit is `|1⟩`. -/
theorem controlled_tensorState_one (U : QMatrix 1) (v : QVector 1) :
    controlled U * tensorState (ket 1) v = tensorState (ket 1) (U * v) := by
  conv_lhs => rw [qvector1_expand v]
  conv_rhs => rw [qvector1_expand v]
  simp only [tensorState_add_right, tensorState_smul_right, Matrix.mul_add, Matrix.mul_smul,
             ket_tensorState]
  rw [controlled_ket_pair_one, controlled_ket_pair_one]

/-- SWAP exchanges the two factors of any product state. -/
theorem SWAP_tensorState (v w : QVector 1) :
    SWAP * tensorState v w = tensorState w v := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  have t110 : (tensorIndexEquiv 1 1).symm 0 = (0, 0) := by decide
  have t111 : (tensorIndexEquiv 1 1).symm 1 = (1, 0) := by decide
  have t112 : (tensorIndexEquiv 1 1).symm 2 = (0, 1) := by decide
  have t113 : (tensorIndexEquiv 1 1).symm 3 = (1, 1) := by decide
  fin_cases r <;>
    simp [SWAP, Matrix.mul_apply, tensorState_apply, Fin.sum_univ_four,
          t110, t111, t112, t113,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

/-- `CNOTRev` is CNOT conjugated by SWAP. -/
theorem CNOTRev_eq_swap_conj : CNOTRev = SWAP * CNOT * SWAP := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CNOTRev, SWAP, CNOT, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Reversed CNOT maps `|a, b⟩` to `|a+b, b⟩` (high qubit controls, low qubit targets).
    Derived from the CNOT action by SWAP conjugation. -/
theorem CNOTRev_ket_pair (a b : Fin 2) :
    CNOTRev * ket (tensorIndexEquiv 1 1 ⟨a, b⟩)
      = ket (tensorIndexEquiv 1 1 ⟨a + b, b⟩) := by
  rw [CNOTRev_eq_swap_conj, ← ket_tensorState, Matrix.mul_assoc, SWAP_tensorState,
      Matrix.mul_assoc, ket_tensorState, CNOT_ket_pair, ← ket_tensorState,
      SWAP_tensorState, ket_tensorState, add_comm b a]

/-- Tdg fixes `|0⟩`. -/
theorem Tdg_ket_zero : Tdg * ket (0 : Fin 2) = ket 0 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Tdg, ket_apply, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Tdg phases `|1⟩` by `e^{-iπ/4}`. -/
theorem Tdg_ket_one :
    Tdg * ket (1 : Fin 2) = Complex.exp (-(Complex.I * Real.pi / 4)) • ket 1 := by
  ext r s; fin_cases r <;> fin_cases s <;>
  simp [Tdg, ket_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

/-- CZ fixes any product state whose HIGH qubit is `|0⟩` (target-side split; CZ is
    control/target symmetric, so both splits exist). -/
theorem CZ_tensorState_zero_right (v : QVector 1) :
    CZ * tensorState v (ket 0 : QVector 1) = tensorState v (ket 0 : QVector 1) := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  have h11 : ∀ i : Fin (2^(1+1)), (tensorIndexEquiv 1 1).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  fin_cases r <;>
    simp [CZ, Matrix.mul_apply, tensorState_apply, Fin.sum_univ_four, h11, ket_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- CZ applies `Z` to the low factor when the HIGH qubit is `|1⟩`. -/
theorem CZ_tensorState_one_right (v : QVector 1) :
    CZ * tensorState v (ket 1 : QVector 1) = tensorState (Z * v) (ket 1 : QVector 1) := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  have h11 : ∀ i : Fin (2^(1+1)), (tensorIndexEquiv 1 1).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  fin_cases r <;>
    simp [CZ, Z, Matrix.mul_apply, tensorState_apply, Fin.sum_univ_four, Fin.sum_univ_two,
          h11, ket_apply, Matrix.vecMul, dotProduct,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- CZ phases a basis pair by `(-1)^(a·b)`: the phase-form action. -/
theorem CZ_ket_pair (a b : Fin 2) :
    CZ * ket (tensorIndexEquiv 1 1 ⟨a, b⟩)
      = ((-1 : ℂ) ^ (a.val * b.val)) • ket (tensorIndexEquiv 1 1 ⟨a, b⟩) := by
  have ha : a = 0 ∨ a = 1 := by omega
  have hb : b = 0 ∨ b = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [te11_00, te11_01, te11_10, te11_11] <;>
    (ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
     rw [mul_ket_apply]
     fin_cases r <;>
       simp [CZ, ket_apply, Matrix.smul_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one])

-- ── Three-qubit gate actions on tensor states ─────────────────────────────────
-- Toffoli/CCZ/Fredkin actions in tensor form. Qubit layout per the LSB convention:
-- for Toffoli/CCZ the state is `(❘a⟩ ⊗ ❘b⟩) ⊗ ❘c⟩` (controls a,b = qubits 0,1); for
-- Fredkin it is `❘a⟩ ⊗ (v ⊗ w)` (control a = qubit 0, swapped targets = qubits 1,2).

/-- Toffoli in tensor form: the target picks up the AND of the controls,
    `|a,b,c⟩ ↦ |a,b,ab+c⟩` (all arithmetic in `Fin 2`). -/
theorem Toffoli_ket_triple (a b c : Fin (2^1)) :
    Toffoli * tensorState (tensorState (ket a) (ket b)) (ket c)
      = tensorState (tensorState (ket a) (ket b)) (ket (a * b + c)) := by
  have h21 : ∀ i : Fin (2^(1+1+1)), (tensorIndexEquiv (1+1) 1).symm i
      = (⟨i.val % 4, by omega⟩, ⟨i.val / 4, by omega⟩) := by decide
  have h11 : ∀ i : Fin (2^(1+1)), (tensorIndexEquiv 1 1).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  have hc : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    (ext r s; obtain rfl : s = 0 := Subsingleton.elim s 0
     fin_cases r <;>
       simp [Toffoli, Matrix.mul_apply, tensorState_apply, Fin.sum_univ_eight,
             h21, h11, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one])

/-- CCZ in tensor form: phase `(-1)^(abc)` on `|a,b,c⟩`. -/
theorem CCZ_ket_triple (a b c : Fin (2^1)) :
    CCZ * tensorState (tensorState (ket a) (ket b)) (ket c)
      = ((-1 : ℂ) ^ (a.val * b.val * c.val))
          • tensorState (tensorState (ket a) (ket b)) (ket c) := by
  have h21 : ∀ i : Fin (2^(1+1+1)), (tensorIndexEquiv (1+1) 1).symm i
      = (⟨i.val % 4, by omega⟩, ⟨i.val / 4, by omega⟩) := by decide
  have h11 : ∀ i : Fin (2^(1+1)), (tensorIndexEquiv 1 1).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  have hc : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    (ext r s; obtain rfl : s = 0 := Subsingleton.elim s 0
     fin_cases r <;>
       simp [CCZ, Matrix.mul_apply, tensorState_apply, Fin.sum_univ_eight,
             h21, h11, ket_apply, Matrix.smul_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one])

/-- Fredkin fixes any product state whose control qubit is `|0⟩`. -/
theorem Fredkin_tensorState_zero (v w : QVector 1) :
    Fredkin * tensorState (ket 0) (tensorState v w)
      = tensorState (ket 0) (tensorState v w) := by
  ext r s; obtain rfl : s = 0 := Subsingleton.elim s 0
  have h12 : ∀ i : Fin (2^(1+(1+1))), (tensorIndexEquiv 1 (1+1)).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  have h11 : ∀ i : Fin (2^(1+1)), (tensorIndexEquiv 1 1).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  fin_cases r <;>
    simp [Fredkin, Matrix.mul_apply, tensorState_apply, Fin.sum_univ_eight,
          h12, h11, ket_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Fredkin swaps the two target factors when the control qubit is `|1⟩`. -/
theorem Fredkin_tensorState_one (v w : QVector 1) :
    Fredkin * tensorState (ket 1) (tensorState v w)
      = tensorState (ket 1) (tensorState w v) := by
  ext r s; obtain rfl : s = 0 := Subsingleton.elim s 0
  have h12 : ∀ i : Fin (2^(1+(1+1))), (tensorIndexEquiv 1 (1+1)).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  have h11 : ∀ i : Fin (2^(1+1)), (tensorIndexEquiv 1 1).symm i
      = (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩) := by decide
  fin_cases r <;>
    simp [Fredkin, Matrix.mul_apply, tensorState_apply, Fin.sum_univ_eight,
          h12, h11, ket_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

-- ── Single-qubit circuit gates ────────────────────────────────────────────────

abbrev HGate : QCircuit 1 := .gate H
abbrev XGate : QCircuit 1 := .gate X
abbrev YGate : QCircuit 1 := .gate Y
abbrev ZGate : QCircuit 1 := .gate Z
abbrev SGate : QCircuit 1 := .gate S
abbrev TGate : QCircuit 1 := .gate T
abbrev TdgGate : QCircuit 1 := .gate Tdg

abbrev RzGate (θ : ℝ) : QCircuit 1 := .gate (Rz θ)
abbrev RxGate (θ : ℝ) : QCircuit 1 := .gate (Rx θ)
abbrev RyGate (θ : ℝ) : QCircuit 1 := .gate (Ry θ)
abbrev RkGate (k : ℕ) : QCircuit 1 := .gate (Rk k)
abbrev SqrtXGate : QCircuit 1 := .gate sqrtX

-- ── Two-qubit circuit gates ───────────────────────────────────────────────────

abbrev CNOTGate : QCircuit 2 := .gate CNOT
abbrev CNOTRevGate : QCircuit 2 := .gate CNOTRev
abbrev CZGate   : QCircuit 2 := .gate CZ
abbrev SWAPGate : QCircuit 2 := .gate SWAP
abbrev SqrtSWAPGate : QCircuit 2 := .gate sqrtSWAP

-- ── Three-qubit circuit gate ──────────────────────────────────────────────────

abbrev ToffoliGate : QCircuit 3 := .gate Toffoli
abbrev CCZGate     : QCircuit 3 := .gate CCZ
abbrev FredkinGate : QCircuit 3 := .gate Fredkin

-- ── Controlled-U circuit gate ─────────────────────────────────────────────────

abbrev ControlledGate (U : QMatrix 1) : QCircuit 2 := .gate (controlled U)

-- ── WF lemmas ─────────────────────────────────────────────────────────────────

@[simp] theorem wf_HGate : QCircuit.WF HGate := isUnitary_H
@[simp] theorem wf_XGate : QCircuit.WF XGate := isUnitary_X
@[simp] theorem wf_YGate : QCircuit.WF YGate := isUnitary_Y
@[simp] theorem wf_ZGate : QCircuit.WF ZGate := isUnitary_Z
@[simp] theorem wf_SGate : QCircuit.WF SGate := isUnitary_S
@[simp] theorem wf_TGate : QCircuit.WF TGate := isUnitary_T

@[simp] theorem wf_RzGate (θ : ℝ) : QCircuit.WF (RzGate θ) := isUnitary_Rz θ
@[simp] theorem wf_RxGate (θ : ℝ) : QCircuit.WF (RxGate θ) := isUnitary_Rx θ
@[simp] theorem wf_RyGate (θ : ℝ) : QCircuit.WF (RyGate θ) := isUnitary_Ry θ
@[simp] theorem wf_RkGate (k : ℕ) : QCircuit.WF (RkGate k) := isUnitary_Rk k

@[simp] theorem wf_CNOTGate : QCircuit.WF CNOTGate := isUnitary_CNOT
@[simp] theorem wf_CNOTRevGate : QCircuit.WF CNOTRevGate := isUnitary_CNOTRev
@[simp] theorem wf_TdgGate : QCircuit.WF TdgGate := isUnitary_Tdg
@[simp] theorem wf_CZGate   : QCircuit.WF CZGate   := isUnitary_CZ
@[simp] theorem wf_SWAPGate : QCircuit.WF SWAPGate := isUnitary_SWAP

@[simp] theorem wf_ToffoliGate : QCircuit.WF ToffoliGate := isUnitary_Toffoli
@[simp] theorem wf_CCZGate     : QCircuit.WF CCZGate     := isUnitary_CCZ
@[simp] theorem wf_FredkinGate : QCircuit.WF FredkinGate := isUnitary_Fredkin
@[simp] theorem wf_SqrtXGate    : QCircuit.WF SqrtXGate    := isUnitary_sqrtX
@[simp] theorem wf_SqrtSWAPGate : QCircuit.WF SqrtSWAPGate := isUnitary_sqrtSWAP

@[simp] theorem wf_ControlledGate {U : QMatrix 1} (hu : IsUnitary U) :
    QCircuit.WF (ControlledGate U) := isUnitary_controlled hu

end QLean

end
