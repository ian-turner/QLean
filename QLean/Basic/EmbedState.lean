import QLean.Basic.Embed
import QLean.Basic.Hilbert
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Bridge: embedded gates acting on states

`Basic/Embed.lean` builds `embed qs U` and its *matrix* algebra. This file connects that
primitive to the *state* layer (`ket`, `QVector`), describing how an embedded gate acts on a
computational basis ket. These are the lemmas circuit-correctness proofs actually use, since the
inputs and intermediate states of an algorithm are (superpositions of) basis kets.

The headline is `embed_diag_mul_ket`: a **diagonal** gate stays diagonal when embedded, acting on
`ket i` by the single scalar `U (selectIdx qs i) (selectIdx qs i)` — no superposition. Every
controlled-phase / rotation gate is diagonal, so this collapses an entire layer of such gates,
however the qubits are addressed, into a scalar phase read off the index bits.
-/

open scoped Matrix
open Classical

noncomputable section

namespace QLean

variable {n k : ℕ}

/-- A diagonal matrix acts on a basis ket by its eigenvalue: `M * ket i = M i i • ket i`. The
    general fact behind every diagonal gate's action on a computational basis state; the embedded
    specialization `embed_diag_mul_ket` is one line away. -/
theorem isDiag_mul_ket {M : QMatrix n} (hM : Matrix.IsDiag M) (i : Fin (2 ^ n)) :
    M * ket i = M i i • ket i := by
  ext r c
  obtain rfl : c = 0 := Subsingleton.elim c 0
  rw [mul_ket_apply, Matrix.smul_apply, ket_apply, smul_eq_mul]
  by_cases hri : r = i
  · subst hri; rw [if_pos rfl, mul_one]
  · rw [if_neg hri, mul_zero]; exact hM hri

-- ── Diagonal embeddings ───────────────────────────────────────────────────────

/-- An embedded gate is diagonal whenever the gate is. The `(i,i)` entry is the gate entry read
    off the selected qubits of `i`; off-diagonal entries vanish because two indices that agree off
    the selected qubits but differ overall must differ on a selected qubit. -/
theorem embed_isDiag {qs : Fin k ↪ Fin n} {U : QMatrix k} (hU : Matrix.IsDiag U) :
    Matrix.IsDiag (embed qs U) := by
  intro i j hij
  rw [embed_apply]
  by_cases h : AgreeOff qs i j
  · rw [if_pos h]
    exact hU fun hsel => hij ((index_ext_iff qs i j).mpr ⟨h, hsel⟩)
  · rw [if_neg h]

/-- A diagonal gate, embedded, acts on a basis ket by a scalar: the gate's eigenvalue on the
    bits selected by `qs`. No superposition is produced, whatever qubits `qs` addresses.
    Reads off the `(i,i)` entry of the (still diagonal) embedding via `isDiag_mul_ket`. -/
theorem embed_diag_mul_ket {qs : Fin k ↪ Fin n} {U : QMatrix k} (hU : Matrix.IsDiag U)
    (i : Fin (2 ^ n)) :
    embed qs U * ket i = U (selectIdx qs i) (selectIdx qs i) • ket i := by
  rw [isDiag_mul_ket (embed_isDiag hU) i, embed_apply, if_pos (AgreeOff.refl qs i)]

-- ── General action on a basis ket ─────────────────────────────────────────────

/-- The action of an embedded gate on a basis ket, expanded over the gate's column at the
    selected bits of `i`: each `s : Fin (2^k)` contributes amplitude `U s (selectIdx qs i)` to the
    index `mergeBits qs i s` (bits `s` on the selected qubits, agreeing with `i` elsewhere).
    The diagonal and single-qubit specializations are the usual entry points. -/
theorem embed_mul_ket (qs : Fin k ↪ Fin n) (U : QMatrix k) (i : Fin (2 ^ n)) :
    embed qs U * ket i = ∑ s : Fin (2 ^ k), U s (selectIdx qs i) • ket (mergeBits qs i s) := by
  ext r c
  obtain rfl : c = 0 := Subsingleton.elim c 0
  rw [mul_ket_apply, embed_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, ket_apply, smul_eq_mul]
  by_cases h : AgreeOff qs r i
  · rw [if_pos h, Finset.sum_eq_single (selectIdx qs r)]
    · rw [mergeBits_selectIdx qs h.symm, if_pos rfl, mul_one]
    · intro s _ hs
      have hne : ¬ r = mergeBits qs i s := fun hr => hs (by
        have := selectIdx_mergeBits qs i s; rw [← hr] at this; exact this.symm)
      rw [if_neg hne, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro s _
    have hne : ¬ r = mergeBits qs i s := fun hr => h (by
      rw [hr]; exact (agreeOff_mergeBits qs i s).symm)
    rw [if_neg hne, mul_zero]

/-- Single-qubit specialization of `embed_mul_ket`: a 1-qubit gate embedded at the qubit `qs 0`
    splits `ket i` into the two indices that clear / set that qubit, weighted by the gate's column
    at the current bit `selectIdx qs i`. The entry point for embedded `H`. -/
theorem embed_single_mul_ket (qs : Fin 1 ↪ Fin n) (U : QMatrix 1) (i : Fin (2 ^ n)) :
    embed qs U * ket i
      = U 0 (selectIdx qs i) • ket (mergeBits qs i 0)
        + U 1 (selectIdx qs i) • ket (mergeBits qs i 1) := by
  rw [embed_mul_ket]; exact Fin.sum_univ_two _

-- ── Acting on the top qubit ───────────────────────────────────────────────────

/-- A 1-qubit gate applied to a basis ket is its column: `U * ket t = U 0 t • ket 0 + U 1 t • ket 1`. -/
theorem mul_ket_one (U : QMatrix 1) (t : Fin (2 ^ 1)) :
    U * ket t = U 0 t • ket 0 + U 1 t • ket 1 := by
  ext r c
  obtain rfl : c = 0 := Subsingleton.elim c 0
  rw [mul_ket_apply]
  fin_cases r <;> simp [Matrix.add_apply, Matrix.smul_apply, ket_apply]

/-- Selecting the single top qubit `Fin.last m` of an `(m+1)`-qubit index reads the high tensor
    factor: it is the bit that `tensorIndexEquiv m 1` places in the top qubit. -/
theorem selectIdx_singleEmb_last {m : ℕ} (j : Fin (2 ^ (m + 1))) :
    selectIdx (singleEmb (Fin.last m)) j = ((tensorIndexEquiv m 1).symm j).2 := by
  apply Fin.ext
  have lhs : (selectIdx (singleEmb (Fin.last m)) j).val = (j : ℕ) / 2 ^ m := by
    unfold selectIdx
    rw [finFunctionFinEquiv_apply_val]
    simp only [singleEmb, Function.Embedding.coeFn_mk, finFunctionFinEquiv_symm_apply_val,
               Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, Fin.val_last,
               Fin.val_zero, pow_zero, mul_one]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (j.isLt.trans_eq (pow_succ 2 m)))
  rw [lhs, tensorIndexEquiv_symm_snd_val]

/-- Reconstructing the top qubit `Fin.last m` to the bit `s` is the tensor pairing: keep the low
    `m` bits of `j` and place `s` in the top qubit. The bridge that turns the embedded top-qubit
    action into a `tensorState`. -/
theorem mergeBits_singleEmb_last {m : ℕ} (j : Fin (2 ^ (m + 1))) (s : Fin (2 ^ 1)) :
    mergeBits (singleEmb (Fin.last m)) j s
      = tensorIndexEquiv m 1 ⟨((tensorIndexEquiv m 1).symm j).1, s⟩ := by
  apply finFunctionFinEquiv.symm.injective
  funext l
  by_cases hl : l = Fin.last m
  · subst hl
    have hmem := mergeBits_bit_mem (singleEmb (Fin.last m)) j s 0
    simp only [singleEmb_apply] at hmem
    rw [hmem]
    apply Fin.ext
    rw [finFunctionFinEquiv_symm_apply_val, finFunctionFinEquiv_symm_apply_val,
        tensorIndexEquiv_apply_val, tensorIndexEquiv_symm_fst_val, Fin.val_last]
    have hjm : (j : ℕ) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (pow_pos (by norm_num) m)
    rw [Nat.add_mul_div_right _ _ (pow_pos (by norm_num) m), Nat.div_eq_of_lt hjm]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Nat.zero_add]
  · have hne : ∀ a, singleEmb (Fin.last m) a ≠ l := by
      intro a; rw [singleEmb_apply]; exact fun h => hl h.symm
    rw [mergeBits_bit_not_mem _ _ _ _ hne]
    apply Fin.ext
    rw [finFunctionFinEquiv_symm_apply_val, finFunctionFinEquiv_symm_apply_val,
        tensorIndexEquiv_apply_val, tensorIndexEquiv_symm_fst_val]
    have hlm : (l : ℕ) < m := by
      have := l.isLt
      rcases Nat.lt_or_ge l.val m with h | h
      · exact h
      · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hl
    have key : (2 : ℕ) ^ m = 2 ^ (l : ℕ) * 2 ^ (m - (l : ℕ)) := by rw [← pow_add]; congr 1; omega
    have hs2 : (s : ℕ) * 2 ^ m = (s.val * 2 ^ (m - (l : ℕ))) * 2 ^ (l : ℕ) := by rw [key]; ring
    rw [hs2, Nat.add_mul_div_right _ _ (pow_pos (by norm_num) (l : ℕ)), key,
        Nat.mod_mul_right_div_self]
    have hK : (s : ℕ) * 2 ^ (m - (l : ℕ)) = 2 * (s.val * 2 ^ (m - 1 - (l : ℕ))) := by
      rw [show (2 : ℕ) ^ (m - (l : ℕ)) = 2 * 2 ^ (m - 1 - (l : ℕ)) from by
        rw [← pow_succ']; congr 1; omega]
      ring
    rw [hK, Nat.add_mul_mod_self_left,
        Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (show m - (l : ℕ) ≠ 0 by omega))]

/-- Action of a 1-qubit gate embedded on the **top** qubit `Fin.last m`: it leaves the low `m`
    qubits as the basis ket of `j`'s low bits and applies `U` to the top qubit. This is the clean
    entry point for the per-qubit layers of a circuit that processes the most significant qubit. -/
theorem embedTop_mul_ket {m : ℕ} (U : QMatrix 1) (j : Fin (2 ^ (m + 1))) :
    embed (singleEmb (Fin.last m)) U * ket j
      = tensorState (ket ((tensorIndexEquiv m 1).symm j).1)
                    (U * ket ((tensorIndexEquiv m 1).symm j).2) := by
  rw [embed_single_mul_ket, selectIdx_singleEmb_last, mergeBits_singleEmb_last,
      mergeBits_singleEmb_last, ← ket_tensorState, ← ket_tensorState,
      mul_ket_one, tensorState_add_right, tensorState_smul_right, tensorState_smul_right]

end QLean

end
