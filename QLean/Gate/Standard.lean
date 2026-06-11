import QLean.Basic.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Matrix

noncomputable section

namespace QLean

-- (Real.sqrt 2 : ℂ)^2 = 2; prerequisite for H unitarity
private lemma sqrt2_sq_cast : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  norm_cast

private lemma sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

-- ── Single-qubit gates ────────────────────────────────────────────────────────

def H : QMatrix 1 :=
  !![(Real.sqrt 2 : ℂ)⁻¹,  (Real.sqrt 2 : ℂ)⁻¹;
     (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

def X : QMatrix 1 := !![0, 1; 1, 0]

def Y : QMatrix 1 := !![0, -Complex.I; Complex.I, 0]

def Z : QMatrix 1 := !![1, 0; 0, -1]

def S : QMatrix 1 := !![1, 0; 0, Complex.I]

def T : QMatrix 1 := !![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)]

noncomputable def Rz (θ : ℝ) : QMatrix 1 :=
  !![Complex.exp (-Complex.I * θ / 2), 0;
     0, Complex.exp (Complex.I * θ / 2)]

noncomputable def Rx (θ : ℝ) : QMatrix 1 :=
  let c : ℂ := Real.cos (θ / 2)
  let s : ℂ := Real.sin (θ / 2)
  !![c, -Complex.I * s; -Complex.I * s, c]

noncomputable def Ry (θ : ℝ) : QMatrix 1 :=
  let c : ℂ := Real.cos (θ / 2)
  let s : ℂ := Real.sin (θ / 2)
  !![c, -s; s, c]

-- ── Two-qubit gates (LSB convention: qubit 0 = low bit) ───────────────────────

-- ctrl = qubit 0 (low bit), tgt = qubit 1 (high bit)
-- Differs from textbook !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0] (MSB ctrl)
def CNOT : QMatrix 2 :=
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0]

-- CZ: phase flip on |11⟩ (index 3); same matrix in both LSB and MSB conventions
def CZ : QMatrix 2 :=
  !![1, 0, 0,  0;
     0, 1, 0,  0;
     0, 0, 1,  0;
     0, 0, 0, -1]

-- SWAP: exchanges qubits 0 and 1; swaps indices 1 and 2
def SWAP : QMatrix 2 :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

-- Three-qubit gate; unitarity deferred to v2
-- ctrl0=qubit0, ctrl1=qubit1, tgt=qubit2; flips tgt when both ctrls=1 (index 7)
def Toffoli : QMatrix 3 :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

-- ── Controlled-U (2-qubit); ctrl=qubit0, tgt=qubit1 ─────────────────────────

-- When ctrl=0: identity on tgt. When ctrl=1: apply U to tgt.
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

theorem isUnitary_X : IsUnitary X := by
  unfold IsUnitary X
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]

theorem isUnitary_Y : IsUnitary Y := by
  unfold IsUnitary Y
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]

theorem isUnitary_Z : IsUnitary Z := by
  unfold IsUnitary Z
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]

theorem isUnitary_CNOT : IsUnitary CNOT := by
  unfold IsUnitary CNOT
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one]

theorem isUnitary_CZ : IsUnitary CZ := by
  unfold IsUnitary CZ
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one]

theorem isUnitary_SWAP : IsUnitary SWAP := by
  unfold IsUnitary SWAP
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one]

set_option maxHeartbeats 800000 in
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

end QLean

end
