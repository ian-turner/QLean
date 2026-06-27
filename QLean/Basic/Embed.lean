import QLean.Basic.Matrix
import Mathlib.Algebra.BigOperators.Fin

/-!
# Embedding gates at selected qubits

`embed qs U` lifts a `k`-qubit gate `U` so that it acts on the `k` qubits picked out
by an injective map `qs : Fin k ↪ Fin n`, leaving the other `n - k` qubits untouched.
This is the addressing primitive that plain `par`/`⊗` cannot express: a non-adjacent
or reordered multi-qubit gate (e.g. a CNOT between qubits `0` and `2`).

The construction is point-wise on matrix entries — no permutation matrices and no
`n - k` subtraction. Writing `selectIdx qs i` for the `Fin (2^k)` index read off the
selected qubits of `i`, and `AgreeOff qs i j` for "`i` and `j` carry the same bits on
every unselected qubit", the entry is

  `embed qs U i j = if AgreeOff qs i j then U (selectIdx qs i) (selectIdx qs j) else 0`.

The algebra (`embed_one`, `embed_mul`, `embed_conjTranspose`) makes `embed_unitary`
immediate, mirroring how `IsUnitary.kron` is assembled in `Basic/Tensor.lean`.
-/

open Classical
open scoped Matrix

noncomputable section

namespace QLean

variable {n k : ℕ}

-- ── Bit selection and the agreement relation ──────────────────────────────────

/-- The `Fin (2^k)` index obtained by reading the `k` qubits selected by `qs` off an
    `n`-qubit index `i` (LSB convention, via `finFunctionFinEquiv`). -/
def selectIdx (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) : Fin (2 ^ k) :=
  finFunctionFinEquiv fun a => finFunctionFinEquiv.symm i (qs a)

/-- Bit `a` of `selectIdx qs i` is bit `qs a` of `i`. -/
lemma selectIdx_symm_apply (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (a : Fin k) :
    finFunctionFinEquiv.symm (selectIdx qs i) a = finFunctionFinEquiv.symm i (qs a) := by
  unfold selectIdx
  rw [Equiv.symm_apply_apply]

/-- If two indices carry the same bits on every selected qubit, their `selectIdx` agree. -/
lemma selectIdx_eq_of_bits (qs : Fin k ↪ Fin n) {i j : Fin (2 ^ n)}
    (h : ∀ a, finFunctionFinEquiv.symm i (qs a) = finFunctionFinEquiv.symm j (qs a)) :
    selectIdx qs i = selectIdx qs j := by
  apply finFunctionFinEquiv.symm.injective
  funext a
  rw [selectIdx_symm_apply, selectIdx_symm_apply]
  exact h a

/-- Two `n`-qubit indices carry the same bits on every qubit *outside* the range of `qs`. -/
def AgreeOff (qs : Fin k ↪ Fin n) (i j : Fin (2 ^ n)) : Prop :=
  ∀ l, (∀ a, qs a ≠ l) → finFunctionFinEquiv.symm i l = finFunctionFinEquiv.symm j l

namespace AgreeOff

lemma refl (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) : AgreeOff qs i i := fun _ _ => rfl

lemma symm {qs : Fin k ↪ Fin n} {i j : Fin (2 ^ n)} (h : AgreeOff qs i j) : AgreeOff qs j i :=
  fun l hl => (h l hl).symm

lemma trans {qs : Fin k ↪ Fin n} {i j m : Fin (2 ^ n)}
    (h₁ : AgreeOff qs i j) (h₂ : AgreeOff qs j m) : AgreeOff qs i m :=
  fun l hl => (h₁ l hl).trans (h₂ l hl)

end AgreeOff

/-- Two indices are equal iff they agree on the selected qubits and on the rest. -/
lemma index_ext_iff (qs : Fin k ↪ Fin n) (i j : Fin (2 ^ n)) :
    i = j ↔ AgreeOff qs i j ∧ selectIdx qs i = selectIdx qs j := by
  constructor
  · rintro rfl
    exact ⟨AgreeOff.refl qs i, rfl⟩
  · rintro ⟨hoff, hsel⟩
    apply finFunctionFinEquiv.symm.injective
    funext l
    by_cases hl : ∃ a, qs a = l
    · obtain ⟨a, rfl⟩ := hl
      rw [← selectIdx_symm_apply qs i a, ← selectIdx_symm_apply qs j a, hsel]
    · push Not at hl
      exact hoff l hl

-- ── The embedding ─────────────────────────────────────────────────────────────

/-- Lift a `k`-qubit gate `U` to act on the qubits selected by `qs : Fin k ↪ Fin n`.
    The `(i, j)` entry is `U` on the selected bits when `i` and `j` agree on every
    unselected qubit, and `0` otherwise. -/
def embed (qs : Fin k ↪ Fin n) (U : QMatrix k) : QMatrix n :=
  fun i j => if AgreeOff qs i j then U (selectIdx qs i) (selectIdx qs j) else 0

lemma embed_apply (qs : Fin k ↪ Fin n) (U : QMatrix k) (i j : Fin (2 ^ n)) :
    embed qs U i j = if AgreeOff qs i j then U (selectIdx qs i) (selectIdx qs j) else 0 :=
  rfl

-- ── Reconstructing an index from selected bits ────────────────────────────────

/-- The index whose selected qubits carry the bits of `s : Fin (2^k)` and whose
    unselected qubits agree with `i`. A one-sided inverse to `selectIdx` on the
    `AgreeOff qs i` fibre. -/
private def mergeBits (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k)) : Fin (2 ^ n) :=
  finFunctionFinEquiv fun l =>
    if h : ∃ a, qs a = l then finFunctionFinEquiv.symm s h.choose
    else finFunctionFinEquiv.symm i l

private lemma mergeBits_bit_mem (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k))
    (a : Fin k) :
    finFunctionFinEquiv.symm (mergeBits qs i s) (qs a) = finFunctionFinEquiv.symm s a := by
  have hca : (⟨a, rfl⟩ : ∃ a', qs a' = qs a).choose = a :=
    qs.injective (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', qs a' = qs a))
  unfold mergeBits
  simp only [Equiv.symm_apply_apply]
  rw [dif_pos ⟨a, rfl⟩, hca]

private lemma mergeBits_bit_not_mem (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k))
    (l : Fin n) (hl : ∀ a, qs a ≠ l) :
    finFunctionFinEquiv.symm (mergeBits qs i s) l = finFunctionFinEquiv.symm i l := by
  unfold mergeBits
  simp only [Equiv.symm_apply_apply]
  rw [dif_neg (fun ⟨a, ha⟩ => hl a ha)]

@[simp] private lemma selectIdx_mergeBits (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k)) :
    selectIdx qs (mergeBits qs i s) = s := by
  apply finFunctionFinEquiv.symm.injective
  funext a
  rw [selectIdx_symm_apply, mergeBits_bit_mem]

private lemma agreeOff_mergeBits (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k)) :
    AgreeOff qs i (mergeBits qs i s) :=
  fun l hl => (mergeBits_bit_not_mem qs i s l hl).symm

private lemma mergeBits_selectIdx (qs : Fin k ↪ Fin n) {i m : Fin (2 ^ n)} (h : AgreeOff qs i m) :
    mergeBits qs i (selectIdx qs m) = m := by
  apply finFunctionFinEquiv.symm.injective
  funext l
  by_cases hl : ∃ a, qs a = l
  · obtain ⟨a, rfl⟩ := hl
    rw [mergeBits_bit_mem, selectIdx_symm_apply]
  · push Not at hl
    rw [mergeBits_bit_not_mem qs i (selectIdx qs m) l hl]
    exact h l hl

-- ── Algebra ───────────────────────────────────────────────────────────────────

/-- Adjoint of an embedded gate is the embedding of the adjoint. -/
theorem embed_conjTranspose (qs : Fin k ↪ Fin n) (U : QMatrix k) :
    (embed qs U)ᴴ = embed qs Uᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, embed_apply, embed_apply]
  by_cases h : AgreeOff qs i j
  · rw [if_pos h.symm, if_pos h, Matrix.conjTranspose_apply]
  · rw [if_neg (fun h' => h h'.symm), if_neg h, star_zero]

/-- Embedding the identity gives the identity. -/
theorem embed_one (qs : Fin k ↪ Fin n) : embed qs (1 : QMatrix k) = 1 := by
  ext i j
  rw [embed_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos (AgreeOff.refl qs _), if_pos rfl, if_pos rfl]
  · rw [if_neg hij]
    by_cases h : AgreeOff qs i j
    · rw [if_pos h, if_neg (fun hs => hij ((index_ext_iff qs i j).mpr ⟨h, hs⟩))]
    · rw [if_neg h]

/-- Embedding is multiplicative on the acted-on qubits. -/
theorem embed_mul (qs : Fin k ↪ Fin n) (A B : QMatrix k) :
    embed qs (A * B) = embed qs A * embed qs B := by
  ext i j
  rw [Matrix.mul_apply, embed_apply]
  by_cases hij : AgreeOff qs i j
  · rw [if_pos hij, Matrix.mul_apply]
    have hf : ∀ m ∈ Finset.univ, m ∉ Finset.univ.filter (AgreeOff qs i ·) →
        embed qs A i m * embed qs B m j = 0 := by
      intro m _ hm
      have h1 : ¬ AgreeOff qs i m := fun hp =>
        hm (Finset.mem_filter.mpr ⟨Finset.mem_univ m, hp⟩)
      rw [embed_apply, if_neg h1, zero_mul]
    rw [← Finset.sum_subset (Finset.filter_subset (AgreeOff qs i ·) Finset.univ) hf]
    refine Finset.sum_nbij' (fun c => mergeBits qs i c) (fun m => selectIdx qs m) ?_ ?_ ?_ ?_ ?_
    · intro c _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, agreeOff_mergeBits qs i c⟩
    · intro m _; exact Finset.mem_univ _
    · intro c _; exact selectIdx_mergeBits qs i c
    · intro m hm; exact mergeBits_selectIdx qs (Finset.mem_filter.mp hm).2
    · intro c _
      have ham : AgreeOff qs i (mergeBits qs i c) := agreeOff_mergeBits qs i c
      have hmj : AgreeOff qs (mergeBits qs i c) j := ham.symm.trans hij
      rw [embed_apply, embed_apply, if_pos ham, if_pos hmj, selectIdx_mergeBits]
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro m _
    rw [embed_apply, embed_apply]
    by_cases h1 : AgreeOff qs i m
    · rw [if_neg (fun h2 => hij (h1.trans h2)), mul_zero]
    · rw [if_neg h1, zero_mul]

/-- A unitary gate stays unitary when embedded. -/
theorem embed_unitary (qs : Fin k ↪ Fin n) {U : QMatrix k} (hU : IsUnitary U) :
    IsUnitary (embed qs U) := by
  unfold IsUnitary
  rw [embed_conjTranspose, ← embed_mul, hU, embed_one]

-- ── Commuting gates on disjoint qubit sets ────────────────────────────────────

/-- If `i` and `l` disagree on a qubit outside both ranges, every term of a mixed
    product vanishes. The shared engine for both orderings in `embed_comm_disjoint`. -/
private lemma embed_comm_zero {n j k : ℕ} (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n)
    (A : QMatrix j) (B : QMatrix k) {i l : Fin (2 ^ n)} {pos : Fin n}
    (h1 : ∀ a, qs₁ a ≠ pos) (h2 : ∀ b, qs₂ b ≠ pos)
    (hne : finFunctionFinEquiv.symm i pos ≠ finFunctionFinEquiv.symm l pos) :
    ∑ m, embed qs₁ A i m * embed qs₂ B m l = 0 := by
  apply Finset.sum_eq_zero
  intro m _
  rw [embed_apply, embed_apply]
  by_cases hA : AgreeOff qs₁ i m
  · by_cases hB : AgreeOff qs₂ m l
    · exact absurd ((hA pos h1).trans (hB pos h2)) hne
    · rw [if_neg hB, mul_zero]
  · rw [if_neg hA, zero_mul]

/-- When `i` and `l` agree outside both ranges, a mixed product collapses to a single
    term: `A` on its qubits times `B` on its qubits. -/
private lemma embed_comm_aux {n j k : ℕ} (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n)
    (hdisj : ∀ (a : Fin j) (b : Fin k), qs₁ a ≠ qs₂ b)
    (A : QMatrix j) (B : QMatrix k) {i l : Fin (2 ^ n)}
    (houter : ∀ pos, (∀ a, qs₁ a ≠ pos) → (∀ b, qs₂ b ≠ pos) →
        finFunctionFinEquiv.symm i pos = finFunctionFinEquiv.symm l pos) :
    ∑ m, embed qs₁ A i m * embed qs₂ B m l
      = A (selectIdx qs₁ i) (selectIdx qs₁ l) * B (selectIdx qs₂ i) (selectIdx qs₂ l) := by
  have hsel₁ : selectIdx qs₁ (mergeBits qs₁ i (selectIdx qs₁ l)) = selectIdx qs₁ l :=
    selectIdx_mergeBits qs₁ i _
  have hsel₂ : selectIdx qs₂ (mergeBits qs₁ i (selectIdx qs₁ l)) = selectIdx qs₂ i :=
    selectIdx_eq_of_bits qs₂ fun b => mergeBits_bit_not_mem qs₁ i _ (qs₂ b) fun a => hdisj a b
  have ha1 : AgreeOff qs₁ i (mergeBits qs₁ i (selectIdx qs₁ l)) := agreeOff_mergeBits qs₁ i _
  have ha2 : AgreeOff qs₂ (mergeBits qs₁ i (selectIdx qs₁ l)) l := by
    intro pos hpos
    by_cases hp : ∃ a, qs₁ a = pos
    · obtain ⟨a, rfl⟩ := hp
      rw [mergeBits_bit_mem, selectIdx_symm_apply]
    · push Not at hp
      rw [mergeBits_bit_not_mem qs₁ i _ pos hp]
      exact houter pos hp hpos
  rw [Finset.sum_eq_single (mergeBits qs₁ i (selectIdx qs₁ l))]
  · rw [embed_apply, embed_apply, if_pos ha1, if_pos ha2, hsel₁, hsel₂]
  · intro m _ hne
    rw [embed_apply, embed_apply]
    by_cases hA : AgreeOff qs₁ i m
    · by_cases hB : AgreeOff qs₂ m l
      · refine absurd ?_ hne
        rw [index_ext_iff qs₁]
        exact ⟨hA.symm.trans ha1,
          (selectIdx_eq_of_bits qs₁ fun a => hB (qs₁ a) fun b => (hdisj a b).symm).trans hsel₁.symm⟩
      · rw [if_neg hB, mul_zero]
    · rw [if_neg hA, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Gates acting on disjoint sets of qubits commute. -/
theorem embed_comm_disjoint {n j k : ℕ} (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n)
    (hdisj : ∀ (a : Fin j) (b : Fin k), qs₁ a ≠ qs₂ b)
    (A : QMatrix j) (B : QMatrix k) :
    embed qs₁ A * embed qs₂ B = embed qs₂ B * embed qs₁ A := by
  ext i l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases houter : ∀ pos, (∀ a, qs₁ a ≠ pos) → (∀ b, qs₂ b ≠ pos) →
      finFunctionFinEquiv.symm i pos = finFunctionFinEquiv.symm l pos
  · rw [embed_comm_aux qs₁ qs₂ hdisj A B houter,
        embed_comm_aux qs₂ qs₁ (fun b a => (hdisj a b).symm) B A
          (fun pos h2 h1 => houter pos h1 h2)]
    ring
  · push Not at houter
    obtain ⟨pos, h1, h2, hne⟩ := houter
    rw [embed_comm_zero qs₁ qs₂ A B h1 h2 hne, embed_comm_zero qs₂ qs₁ B A h2 h1 hne]

end QLean

end
