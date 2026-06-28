import QLean.Basic.Matrix
import QLean.Basic.Tensor
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

-- ── Common embeddings: single qubit and a qubit pair ──────────────────────────

/-- Embed a 1-qubit gate at a single qubit `t`. Injectivity is automatic on `Fin 1`. -/
def singleEmb (t : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => t, fun a b _ => Subsingleton.elim a b⟩

@[simp] lemma singleEmb_apply (t : Fin n) (a : Fin 1) : singleEmb t a = t := rfl

/-- Embed a 2-qubit gate at distinct qubits `a` (gate-qubit `0`) and `b` (gate-qubit `1`). -/
def pairEmb (a b : Fin n) (h : a ≠ b) : Fin 2 ↪ Fin n :=
  ⟨![a, b], by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]⟩

@[simp] lemma pairEmb_apply_zero (a b : Fin n) (h : a ≠ b) : pairEmb a b h 0 = a := rfl
@[simp] lemma pairEmb_apply_one (a b : Fin n) (h : a ≠ b) : pairEmb a b h 1 = b := rfl

-- ── Reconstructing an index from selected bits ────────────────────────────────

/-- The index whose selected qubits carry the bits of `s : Fin (2^k)` and whose
    unselected qubits agree with `i`. A one-sided inverse to `selectIdx` on the
    `AgreeOff qs i` fibre, and the public address-reconstruction primitive that the
    state-action lemmas in `Basic/EmbedState.lean` are phrased with. -/
def mergeBits (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k)) : Fin (2 ^ n) :=
  finFunctionFinEquiv fun l =>
    if h : ∃ a, qs a = l then finFunctionFinEquiv.symm s h.choose
    else finFunctionFinEquiv.symm i l

/-- On a selected qubit `qs a`, `mergeBits qs i s` carries bit `a` of `s`. -/
lemma mergeBits_bit_mem (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k))
    (a : Fin k) :
    finFunctionFinEquiv.symm (mergeBits qs i s) (qs a) = finFunctionFinEquiv.symm s a := by
  have hca : (⟨a, rfl⟩ : ∃ a', qs a' = qs a).choose = a :=
    qs.injective (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', qs a' = qs a))
  unfold mergeBits
  simp only [Equiv.symm_apply_apply]
  rw [dif_pos ⟨a, rfl⟩, hca]

/-- On an unselected qubit `l`, `mergeBits qs i s` carries bit `l` of `i`. -/
lemma mergeBits_bit_not_mem (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k))
    (l : Fin n) (hl : ∀ a, qs a ≠ l) :
    finFunctionFinEquiv.symm (mergeBits qs i s) l = finFunctionFinEquiv.symm i l := by
  unfold mergeBits
  simp only [Equiv.symm_apply_apply]
  rw [dif_neg (fun ⟨a, ha⟩ => hl a ha)]

@[simp] lemma selectIdx_mergeBits (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k)) :
    selectIdx qs (mergeBits qs i s) = s := by
  apply finFunctionFinEquiv.symm.injective
  funext a
  rw [selectIdx_symm_apply, mergeBits_bit_mem]

lemma agreeOff_mergeBits (qs : Fin k ↪ Fin n) (i : Fin (2 ^ n)) (s : Fin (2 ^ k)) :
    AgreeOff qs i (mergeBits qs i s) :=
  fun l hl => (mergeBits_bit_not_mem qs i s l hl).symm

lemma mergeBits_selectIdx (qs : Fin k ↪ Fin n) {i m : Fin (2 ^ n)} (h : AgreeOff qs i m) :
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

-- ── Composition of embeddings ─────────────────────────────────────────────────

/-- Selecting through a composed embedding factors: reading the bits of `qs2.trans qs`
    is reading the bits of `qs2` off the index already restricted by `qs`. -/
lemma selectIdx_trans {m : ℕ} (qs : Fin k ↪ Fin n) (qs2 : Fin m ↪ Fin k) (i : Fin (2 ^ n)) :
    selectIdx (qs2.trans qs) i = selectIdx qs2 (selectIdx qs i) := by
  apply finFunctionFinEquiv.symm.injective
  funext a
  rw [selectIdx_symm_apply, selectIdx_symm_apply, selectIdx_symm_apply,
      Function.Embedding.trans_apply]

/-- Embedding through a composition is the embedding through the composed address map:
    `embed qs (embed qs2 U) = embed (qs2.trans qs) U`. -/
theorem embed_embed {m : ℕ} (qs : Fin k ↪ Fin n) (qs2 : Fin m ↪ Fin k) (U : QMatrix m) :
    embed qs (embed qs2 U) = embed (qs2.trans qs) U := by
  ext i j
  rw [embed_apply qs (embed qs2 U) i j, embed_apply (qs2.trans qs) U i j]
  by_cases htrans : AgreeOff (qs2.trans qs) i j
  · have hqs : AgreeOff qs i j := fun l hl =>
      htrans l (fun a => by rw [Function.Embedding.trans_apply]; exact hl (qs2 a))
    have hagree2 : AgreeOff qs2 (selectIdx qs i) (selectIdx qs j) := by
      intro b hb
      rw [selectIdx_symm_apply, selectIdx_symm_apply]
      exact htrans (qs b) (fun a heq =>
        hb a (qs.injective (by rw [← Function.Embedding.trans_apply]; exact heq)))
    rw [if_pos hqs, if_pos htrans, embed_apply, if_pos hagree2,
        selectIdx_trans, selectIdx_trans]
  · rw [if_neg htrans]
    by_cases hqs : AgreeOff qs i j
    · rw [if_pos hqs, embed_apply, if_neg]
      unfold AgreeOff at htrans
      push Not at htrans
      obtain ⟨l, hltrans, hne⟩ := htrans
      by_cases hlrange : ∃ b, qs b = l
      · obtain ⟨b, rfl⟩ := hlrange
        intro hagree2
        apply hne
        have hb : ∀ a, qs2 a ≠ b := fun a heq =>
          hltrans a (by rw [Function.Embedding.trans_apply, heq])
        have hh := hagree2 b hb
        rwa [selectIdx_symm_apply, selectIdx_symm_apply] at hh
      · push Not at hlrange
        exact absurd (hqs l hlrange) hne
    · rw [if_neg hqs]

-- ── Split-coordinate embeddings for the tensor factoring ───────────────────────

/-- The low `j` of `j + k` coordinates, value-preserving (`Fin.castAdd`). -/
def lowEmb (j k : ℕ) : Fin j ↪ Fin (j + k) :=
  ⟨Fin.castAdd k, Fin.castAdd_injective j k⟩

/-- The high `k` of `j + k` coordinates, shifted up by `j` (`Fin.natAdd`). -/
def highEmb (j k : ℕ) : Fin k ↪ Fin (j + k) :=
  ⟨Fin.natAdd j, Fin.natAdd_injective k j⟩

@[simp] lemma lowEmb_apply (j k : ℕ) (a : Fin j) : lowEmb j k a = Fin.castAdd k a := rfl
@[simp] lemma highEmb_apply (j k : ℕ) (b : Fin k) : highEmb j k b = Fin.natAdd j b := rfl

/-- Bit `a` (for `a : Fin j`) of the low tensor factor of `S` is bit `castAdd k a` of `S`:
    the low `j` bits are kept unchanged by the `mod 2^j` split. -/
lemma tensor_symm_fst_bit (j k : ℕ) (S : Fin (2 ^ (j + k))) (a : Fin j) :
    finFunctionFinEquiv.symm ((tensorIndexEquiv j k).symm S).1 a
      = finFunctionFinEquiv.symm S (Fin.castAdd k a) := by
  apply Fin.ext
  rw [finFunctionFinEquiv_symm_apply_val, finFunctionFinEquiv_symm_apply_val,
      tensorIndexEquiv_symm_fst_val, Fin.val_castAdd]
  have hpow : (2 : ℕ) ^ j = 2 ^ (a : ℕ) * 2 ^ (j - (a : ℕ)) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (show j - (a : ℕ) ≠ 0 by omega))]

/-- Bit `b` (for `b : Fin k`) of the high tensor factor of `S` is bit `natAdd j b` of `S`:
    the high `k` bits are the `div 2^j` shift. -/
lemma tensor_symm_snd_bit (j k : ℕ) (S : Fin (2 ^ (j + k))) (b : Fin k) :
    finFunctionFinEquiv.symm ((tensorIndexEquiv j k).symm S).2 b
      = finFunctionFinEquiv.symm S (Fin.natAdd j b) := by
  apply Fin.ext
  rw [finFunctionFinEquiv_symm_apply_val, finFunctionFinEquiv_symm_apply_val,
      tensorIndexEquiv_symm_snd_val, Fin.val_natAdd, Nat.div_div_eq_div_mul, ← pow_add]

/-- `selectIdx` through the low split embedding is the low tensor factor of `selectIdx qs`. -/
lemma selectIdx_lowEmb {j : ℕ} (qs : Fin (j + k) ↪ Fin n) (s : Fin (2 ^ n)) :
    selectIdx ((lowEmb j k).trans qs) s
      = ((tensorIndexEquiv j k).symm (selectIdx qs s)).1 := by
  apply finFunctionFinEquiv.symm.injective
  funext a
  rw [selectIdx_symm_apply, Function.Embedding.trans_apply, tensor_symm_fst_bit,
      selectIdx_symm_apply, lowEmb_apply]

/-- `selectIdx` through the high split embedding is the high tensor factor of `selectIdx qs`. -/
lemma selectIdx_highEmb {j : ℕ} (qs : Fin (j + k) ↪ Fin n) (s : Fin (2 ^ n)) :
    selectIdx ((highEmb j k).trans qs) s
      = ((tensorIndexEquiv j k).symm (selectIdx qs s)).2 := by
  apply finFunctionFinEquiv.symm.injective
  funext b
  rw [selectIdx_symm_apply, Function.Embedding.trans_apply, tensor_symm_snd_bit,
      selectIdx_symm_apply, highEmb_apply]

/-- Factoring a parallel (`kron`) gate through an embedding: embedding `A ⊗ B` at `qs` is the
    product of `A` embedded at the low half of `qs` and `B` embedded at the high half. -/
theorem embed_kron_factor {j : ℕ} (qs : Fin (j + k) ↪ Fin n) (A : QMatrix j) (B : QMatrix k) :
    embed qs (kron A B)
      = embed ((lowEmb j k).trans qs) A * embed ((highEmb j k).trans qs) B := by
  have hdisj : ∀ (a : Fin j) (b : Fin k),
      ((lowEmb j k).trans qs) a ≠ ((highEmb j k).trans qs) b := by
    intro a b heq
    rw [Function.Embedding.trans_apply, Function.Embedding.trans_apply] at heq
    have hv := congrArg Fin.val (qs.injective heq)
    simp only [lowEmb_apply, highEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  ext i l
  rw [Matrix.mul_apply]
  by_cases hA : AgreeOff qs i l
  · have houter : ∀ pos, (∀ a, ((lowEmb j k).trans qs) a ≠ pos) →
        (∀ b, ((highEmb j k).trans qs) b ≠ pos) →
        finFunctionFinEquiv.symm i pos = finFunctionFinEquiv.symm l pos := by
      intro pos h1 h2
      refine hA pos ?_
      intro c
      refine Fin.addCases (motive := fun c => qs c ≠ pos) (fun a => ?_) (fun b => ?_) c
      · exact h1 a
      · exact h2 b
    rw [embed_apply, if_pos hA,
        embed_comm_aux ((lowEmb j k).trans qs) ((highEmb j k).trans qs) hdisj A B houter]
    simp only [kron, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    rw [← selectIdx_lowEmb, ← selectIdx_lowEmb, ← selectIdx_highEmb, ← selectIdx_highEmb]
  · rw [embed_apply, if_neg hA]
    unfold AgreeOff at hA
    push Not at hA
    obtain ⟨pos, hposqs, hne⟩ := hA
    have h1 : ∀ a, ((lowEmb j k).trans qs) a ≠ pos := by
      intro a
      rw [Function.Embedding.trans_apply]
      exact hposqs ((lowEmb j k) a)
    have h2 : ∀ b, ((highEmb j k).trans qs) b ≠ pos := by
      intro b
      rw [Function.Embedding.trans_apply]
      exact hposqs ((highEmb j k) b)
    rw [embed_comm_zero ((lowEmb j k).trans qs) ((highEmb j k).trans qs) A B h1 h2 hne]

-- ── The identity embedding and `kron` as a product of two embeddings ───────────

/-- Selecting through the identity embedding (all qubits, in order) is the identity. -/
@[simp] lemma selectIdx_refl (i : Fin (2 ^ n)) :
    selectIdx (Function.Embedding.refl (Fin n)) i = i := by
  apply finFunctionFinEquiv.symm.injective
  funext a
  rw [selectIdx_symm_apply]
  rfl

/-- Embedding through the identity embedding leaves the gate unchanged. -/
theorem embed_refl (U : QMatrix n) : embed (Function.Embedding.refl (Fin n)) U = U := by
  ext i j
  have hagree : AgreeOff (Function.Embedding.refl (Fin n)) i j := fun l hl => (hl l rfl).elim
  rw [embed_apply, if_pos hagree, selectIdx_refl, selectIdx_refl]

/-- A tensor product is the product of its two factors embedded at the low/high coordinate blocks —
    the matrix form behind `QCircuit.par_as_embed` (a special case of `embed_kron_factor` at the
    identity embedding). -/
theorem kron_eq_embed {j k : ℕ} (A : QMatrix j) (B : QMatrix k) :
    kron A B = embed (lowEmb j k) A * embed (highEmb j k) B := by
  have h := embed_kron_factor (Function.Embedding.refl (Fin (j + k))) A B
  rw [embed_refl] at h
  exact h

end QLean

end
