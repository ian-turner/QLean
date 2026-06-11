import QLean.Gate.Standard
import Mathlib.Logic.Equiv.Fin.Basic

open Classical
open scoped Matrix

noncomputable section

namespace QLean

-- ── gateAt definition ────────────────────────────────────────────────────────

/-- Apply a `k`-qubit gate `U` to the qubits selected by `qs : Fin k ↪ Fin n`.
    Rows/columns must agree on the complement of `range qs`; otherwise the entry is 0. -/
def gateAt {n k : ℕ} (qs : Fin k ↪ Fin n) (U : QMatrix k) : QMatrix n :=
  fun i j =>
    U (finFunctionFinEquiv (finFunctionFinEquiv.symm i ∘ qs))
      (finFunctionFinEquiv (finFunctionFinEquiv.symm j ∘ qs)) *
    if ∀ l : Fin n, (∀ m : Fin k, qs m ≠ l) → finFunctionFinEquiv.symm i l = finFunctionFinEquiv.symm j l
    then 1 else 0

/-- Project a row/column index onto the selected qubits. -/
private abbrev π {n k : ℕ} (qs : Fin k ↪ Fin n) (x : Fin (2^n)) : Fin (2^k) :=
  finFunctionFinEquiv (finFunctionFinEquiv.symm x ∘ qs)

/-- "Complement condition": indices `a` and `b` agree on every qubit outside `range qs`. -/
private abbrev cc {n k : ℕ} (qs : Fin k ↪ Fin n) (a b : Fin (2^n)) : Prop :=
  ∀ l : Fin n, (∀ m : Fin k, qs m ≠ l) → finFunctionFinEquiv.symm a l = finFunctionFinEquiv.symm b l

@[simp] private lemma gateAt_eq {n k : ℕ} (qs : Fin k ↪ Fin n) (U : QMatrix k) (i j : Fin (2^n)) :
    gateAt qs U i j = U (π qs i) (π qs j) * if cc qs i j then 1 else 0 := rfl

/-- Complement condition is symmetric. -/
private lemma cc_symm {n k : ℕ} (qs : Fin k ↪ Fin n) (a b : Fin (2^n)) :
    cc qs a b ↔ cc qs b a :=
  ⟨fun h l hl => (h l hl).symm, fun h l hl => (h l hl).symm⟩

/-- Complement condition is transitive. -/
private lemma cc_trans {n k : ℕ} (qs : Fin k ↪ Fin n) {a b c : Fin (2^n)} :
    cc qs a b → cc qs b c → cc qs a c :=
  fun hab hbc l hl => (hab l hl).trans (hbc l hl)

private lemma cc_iff_of_ab {n k : ℕ} (qs : Fin k ↪ Fin n) {a b : Fin (2^n)} (l : Fin (2^n))
    (hab : cc qs a b) : cc qs a l ↔ cc qs l b :=
  ⟨fun h => cc_trans qs ((cc_symm qs a l).mp h) hab,
   fun h => cc_trans qs hab ((cc_symm qs l b).mp h)⟩

-- ── mergeBits helper ──────────────────────────────────────────────────────────

/-- Build a row index from complement bits `c` (outside `qs`) and selected bits `s` (inside `qs`). -/
private def mergeBits {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) : Fin (2^n) :=
  finFunctionFinEquiv (fun l =>
    if h : ∃ a : Fin k, qs a = l then s h.choose else c l)

private lemma mb_sel {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) (m : Fin k) :
    finFunctionFinEquiv.symm (mergeBits qs c s) (qs m) = s m := by
  simp only [mergeBits, Equiv.symm_apply_apply]
  rw [dif_pos ⟨m, rfl⟩]
  exact congr_arg s (qs.injective ((⟨m, rfl⟩ : ∃ a : Fin k, qs a = qs m).choose_spec))

private lemma mb_comp {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) (l : Fin n) (hl : ∀ a : Fin k, qs a ≠ l) :
    finFunctionFinEquiv.symm (mergeBits qs c s) l = c l := by
  simp only [mergeBits, Equiv.symm_apply_apply]
  exact dif_neg (fun ⟨a, ha⟩ => hl a ha)

private lemma π_mb {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) :
    π qs (mergeBits qs c s) = finFunctionFinEquiv s := by
  simp only [π]
  suffices h : finFunctionFinEquiv.symm (mergeBits qs c s) ∘ qs = s by rw [h]
  funext m; exact mb_sel qs c s m

private lemma mb_rt {n k : ℕ} (qs : Fin k ↪ Fin n) (i : Fin (2^n)) :
    mergeBits qs (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm i ∘ qs) = i := by
  apply finFunctionFinEquiv.symm.injective
  funext l
  simp only [mergeBits, Equiv.symm_apply_apply]
  split_ifs with h
  · exact congr_arg (finFunctionFinEquiv.symm i) h.choose_spec
  · rfl

private lemma cc_mb {n k : ℕ} (qs : Fin k ↪ Fin n) (i : Fin (2^n)) (s : Fin k → Fin 2) :
    cc qs i (mergeBits qs (finFunctionFinEquiv.symm i) s) :=
  fun l hl => (mb_comp qs _ s l hl).symm

private lemma mb_π {n k : ℕ} (qs : Fin k ↪ Fin n) (i l : Fin (2^n)) (hcl : cc qs i l) :
    mergeBits qs (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm (π qs l)) = l := by
  apply finFunctionFinEquiv.symm.injective
  funext pos
  simp only [mergeBits, π, Equiv.symm_apply_apply]
  split_ifs with hq
  · exact congr_arg (finFunctionFinEquiv.symm l) hq.choose_spec
  · exact hcl pos (fun a ha => hq ⟨a, ha⟩)

-- ── gateAt_conjTranspose ──────────────────────────────────────────────────────

/-- Adjoint of `gateAt qs U` is `gateAt qs Uᴴ`. -/
theorem gateAt_conjTranspose {n k : ℕ} (qs : Fin k ↪ Fin n) (U : QMatrix k) :
    (gateAt qs U)ᴴ = gateAt qs Uᴴ := by
  ext i j
  by_cases h : cc qs i j
  · have h' : cc qs j i := (cc_symm qs i j).mp h
    simp only [gateAt_eq, Matrix.conjTranspose_apply, if_pos h, if_pos h', mul_one]
  · have h' : ¬cc qs j i := fun hji => h ((cc_symm qs j i).mp hji)
    simp only [gateAt_eq, Matrix.conjTranspose_apply, if_neg h, if_neg h', mul_zero, star_zero]

-- ── gateAt_one ───────────────────────────────────────────────────────────────

/-- `gateAt` of the identity matrix is the identity. -/
theorem gateAt_one {n k : ℕ} (qs : Fin k ↪ Fin n) : gateAt qs (1 : QMatrix k) = 1 := by
  ext i j
  simp only [gateAt_eq, Matrix.one_apply]
  by_cases hcc : cc qs i j
  · simp only [if_pos hcc, mul_one]
    by_cases hproj : π qs i = π qs j
    · simp only [hproj, ↓reduceIte]
      have hij : i = j := by
        apply finFunctionFinEquiv.symm.injective
        funext l
        by_cases hm : ∃ m : Fin k, qs m = l
        · obtain ⟨m, rfl⟩ := hm
          exact congr_fun (finFunctionFinEquiv.injective hproj) m
        · exact hcc l (fun m hml => hm ⟨m, hml⟩)
      simp [hij]
    · simp only [if_neg hproj]
      have hne : i ≠ j := fun hij => hproj (congr_arg (π qs) hij)
      simp [hne]
  · simp only [if_neg hcc, mul_zero]
    have hne : i ≠ j := fun hij => hcc (hij ▸ fun _ _ => rfl)
    simp [hne]

-- ── gateAt_mul ───────────────────────────────────────────────────────────────

/-- `gateAt` is a ring homomorphism on the embedded qubits (used for unitarity and commutativity). -/
theorem gateAt_mul {n k : ℕ} (qs : Fin k ↪ Fin n) (A B : QMatrix k) :
    gateAt qs (A * B) = gateAt qs A * gateAt qs B := by
  ext i j
  simp only [gateAt_eq, Matrix.mul_apply]
  by_cases hcc : cc qs i j
  · simp only [if_pos hcc, mul_one]
    have hind : ∀ l : Fin (2^n),
        (A (π qs i) (π qs l) * (if cc qs i l then (1:ℂ) else 0)) *
        (B (π qs l) (π qs j) * (if cc qs l j then 1 else 0)) =
        A (π qs i) (π qs l) * B (π qs l) (π qs j) * (if cc qs i l then 1 else 0) := fun l => by
      by_cases hil : cc qs i l
      · have hlj : cc qs l j := (cc_iff_of_ab qs l hcc).mp hil
        simp [if_pos hil, if_pos hlj]
      · have hlj : ¬cc qs l j := fun hlj' => hil ((cc_iff_of_ab qs l hcc).mpr hlj')
        simp [if_neg hil, if_neg hlj]
    simp only [hind]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    let emb := fun m : Fin (2^k) =>
      mergeBits qs (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm m)
    have hπ : ∀ m : Fin (2^k), π qs (emb m) = m := fun m => by
      simp only [emb, π_mb]; simp
    apply Finset.sum_nbij emb
    · intro m _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact cc_mb qs i _
    · intro m₁ _ m₂ _ h
      have := congr_arg (π qs) h; rwa [hπ, hπ] at this
    · intro l hl
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact ⟨π qs l, Finset.mem_coe.mpr (Finset.mem_univ _), mb_π qs i l hl⟩
    · intro m _
      simp only [hπ]
  · simp only [if_neg hcc, mul_zero]
    symm
    apply Finset.sum_eq_zero; intro l _
    by_cases hil : cc qs i l
    · have hjl : ¬cc qs l j := fun hlj => hcc (cc_trans qs hil hlj)
      simp [if_neg hjl]
    · simp [if_neg hil]

-- ── gateAt_unitary ───────────────────────────────────────────────────────────

/-- A unitary gate embedded via `gateAt` remains unitary on the larger system. -/
theorem gateAt_unitary {n k : ℕ} (qs : Fin k ↪ Fin n) {U : QMatrix k}
    (hu : IsUnitary U) : IsUnitary (gateAt qs U) := by
  unfold IsUnitary
  rw [gateAt_conjTranspose, ← gateAt_mul, hu, gateAt_one]

-- ── Embedding helpers ─────────────────────────────────────────────────────────

/-- Embed qubit `i` as the unique element of `Fin 1`. -/
private def singletonEmbed {n : ℕ} (i : Fin n) : Fin 1 ↪ Fin n :=
  ⟨Fin.cases i Fin.elim0, by intro a b _; fin_cases a <;> fin_cases b <;> simp⟩

/-- Embed `ctrl` and `tgt` as the two elements of `Fin 2` (ctrl=0, tgt=1). -/
private def pairEmbed {n : ℕ} (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : Fin 2 ↪ Fin n :=
  ⟨![ctrl, tgt], by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]⟩

-- ── Convenience wrappers ──────────────────────────────────────────────────────

/-- Hadamard gate acting on qubit `i` of an `n`-qubit system. -/
def hadamardAt {n : ℕ} (i : Fin n) : QMatrix n := gateAt (singletonEmbed i) H
/-- CNOT gate with control qubit `ctrl` and target qubit `tgt`. -/
def cnotAt {n : ℕ} (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : QMatrix n :=
  gateAt (pairEmbed ctrl tgt h) CNOT
/-- Controlled-U gate with control qubit `ctrl` and target qubit `tgt`. -/
def controlledAt {n : ℕ} (ctrl tgt : Fin n) (h : ctrl ≠ tgt) (U : QMatrix 1) : QMatrix n :=
  gateAt (pairEmbed ctrl tgt h) (controlled U)

theorem isUnitary_hadamardAt {n : ℕ} (i : Fin n) : IsUnitary (hadamardAt i) :=
  gateAt_unitary _ isUnitary_H

theorem isUnitary_cnotAt {n : ℕ} (ctrl tgt : Fin n) (h : ctrl ≠ tgt) :
    IsUnitary (cnotAt ctrl tgt h) :=
  gateAt_unitary _ isUnitary_CNOT

theorem isUnitary_controlledAt {n : ℕ} (ctrl tgt : Fin n) (h : ctrl ≠ tgt) {U : QMatrix 1}
    (hu : IsUnitary U) : IsUnitary (controlledAt ctrl tgt h U) :=
  gateAt_unitary _ (isUnitary_controlled hu)

-- ── gateAt_comm_disjoint ──────────────────────────────────────────────────────

/-- Intermediate index agreeing with `l` on `qs₁` bits and with `i` on `qs₂` bits. -/
private noncomputable def commMid {n j k : ℕ}
    (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n) (i l : Fin (2^n)) : Fin (2^n) :=
  finFunctionFinEquiv (fun pos =>
    if ∃ a : Fin j, qs₁ a = pos then finFunctionFinEquiv.symm l pos
    else finFunctionFinEquiv.symm i pos)

/-- Gates on disjoint qubit sets commute. -/
theorem gateAt_comm_disjoint {n j k : ℕ} (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n)
    (hdisj : Disjoint (Set.range qs₁) (Set.range qs₂))
    (A : QMatrix j) (B : QMatrix k) :
    gateAt qs₁ A * gateAt qs₂ B = gateAt qs₂ B * gateAt qs₁ A := by
  have hd : ∀ (a : Fin j) (b : Fin k), qs₁ a ≠ qs₂ b := fun a b hab =>
    Set.disjoint_left.mp hdisj (Set.mem_range_self a) ⟨b, hab.symm⟩
  ext i l
  simp only [Matrix.mul_apply, gateAt_eq]
  by_cases houter : ∀ pos : Fin n,
      (∀ a : Fin j, qs₁ a ≠ pos) → (∀ b : Fin k, qs₂ b ≠ pos) →
      finFunctionFinEquiv.symm i pos = finFunctionFinEquiv.symm l pos
  · set mid₁₂ := commMid qs₁ qs₂ i l
    set mid₂₁ := commMid qs₂ qs₁ i l
    -- Helper lemmas for mid₁₂
    have hcc₁_i : cc qs₁ i mid₁₂ := by
      intro pos hpos
      simp only [mid₁₂, commMid, Equiv.symm_apply_apply]
      have : ¬∃ a : Fin j, qs₁ a = pos := fun ⟨a, ha⟩ => hpos a ha
      simp [this]
    have hcc₂_l : cc qs₂ mid₁₂ l := by
      intro pos hpos
      simp only [mid₁₂, commMid, Equiv.symm_apply_apply]
      by_cases hq1 : ∃ a : Fin j, qs₁ a = pos
      · simp [hq1]
      · rw [if_neg hq1]; exact houter pos (not_exists.mp hq1) hpos
    have hπ₁_l : π qs₁ mid₁₂ = π qs₁ l := by
      simp only [π, mid₁₂, commMid, Equiv.symm_apply_apply]
      congr 1; funext m; simp [show ∃ a : Fin j, qs₁ a = qs₁ m from ⟨m, rfl⟩]
    have hπ₂_i : π qs₂ mid₁₂ = π qs₂ i := by
      simp only [π, mid₁₂, commMid, Equiv.symm_apply_apply]
      congr 1; funext m
      have hne : ¬∃ a : Fin j, qs₁ a = qs₂ m := fun ⟨a, ha⟩ => hd a m ha
      simp [hne]
    -- Helper lemmas for mid₂₁
    have hcc₂_i : cc qs₂ i mid₂₁ := by
      intro pos hpos
      simp only [mid₂₁, commMid, Equiv.symm_apply_apply]
      have : ¬∃ b : Fin k, qs₂ b = pos := fun ⟨b, hb⟩ => hpos b hb
      simp [this]
    have hcc₁_l : cc qs₁ mid₂₁ l := by
      intro pos hpos
      simp only [mid₂₁, commMid, Equiv.symm_apply_apply]
      by_cases hq2 : ∃ b : Fin k, qs₂ b = pos
      · rw [if_pos hq2]
      · rw [if_neg hq2]; exact houter pos hpos (not_exists.mp hq2)
    have hπ₂_l' : π qs₂ mid₂₁ = π qs₂ l := by
      simp only [π, mid₂₁, commMid, Equiv.symm_apply_apply]
      congr 1; funext m; simp [show ∃ b : Fin k, qs₂ b = qs₂ m from ⟨m, rfl⟩]
    have hπ₁_i' : π qs₁ mid₂₁ = π qs₁ i := by
      simp only [π, mid₂₁, commMid, Equiv.symm_apply_apply]
      congr 1; funext m
      have hne : ¬∃ b : Fin k, qs₂ b = qs₁ m := fun ⟨b, hb⟩ => hd m b hb.symm
      simp [hne]
    -- Both sums reduce to single terms; conclude by commutativity
    have hab : ∑ mid : Fin (2^n),
        (A (π qs₁ i) (π qs₁ mid) * if cc qs₁ i mid then 1 else 0) *
        (B (π qs₂ mid) (π qs₂ l) * if cc qs₂ mid l then 1 else 0) =
        A (π qs₁ i) (π qs₁ l) * B (π qs₂ i) (π qs₂ l) := by
      rw [Finset.sum_eq_single mid₁₂ _ (fun h => absurd (Finset.mem_univ _) h)]
      · rw [hπ₁_l, hπ₂_i, if_pos hcc₁_i, if_pos hcc₂_l]; ring
      · intro mid _ hmid
        by_cases h1 : cc qs₁ i mid
        · by_cases h2 : cc qs₂ mid l
          · exfalso; apply hmid
            apply finFunctionFinEquiv.symm.injective; funext pos
            simp only [mid₁₂, commMid, Equiv.symm_apply_apply]
            by_cases hq1 : ∃ a : Fin j, qs₁ a = pos
            · rw [if_pos hq1]
              obtain ⟨a, rfl⟩ := hq1
              exact h2 (qs₁ a) (fun b hb => hd a b hb.symm)
            · rw [if_neg hq1]; exact (h1 pos (not_exists.mp hq1)).symm
          · simp [if_neg h2]
        · simp [if_neg h1]
    have hba : ∑ mid : Fin (2^n),
        (B (π qs₂ i) (π qs₂ mid) * if cc qs₂ i mid then 1 else 0) *
        (A (π qs₁ mid) (π qs₁ l) * if cc qs₁ mid l then 1 else 0) =
        B (π qs₂ i) (π qs₂ l) * A (π qs₁ i) (π qs₁ l) := by
      rw [Finset.sum_eq_single mid₂₁ _ (fun h => absurd (Finset.mem_univ _) h)]
      · rw [hπ₂_l', hπ₁_i', if_pos hcc₂_i, if_pos hcc₁_l]; ring
      · intro mid _ hmid
        by_cases h2 : cc qs₂ i mid
        · by_cases h1 : cc qs₁ mid l
          · exfalso; apply hmid
            apply finFunctionFinEquiv.symm.injective; funext pos
            simp only [mid₂₁, commMid, Equiv.symm_apply_apply]
            by_cases hq2 : ∃ b : Fin k, qs₂ b = pos
            · rw [if_pos hq2]
              obtain ⟨b, rfl⟩ := hq2
              exact h1 (qs₂ b) (fun a => hd a b)
            · rw [if_neg hq2]; exact (h2 pos (not_exists.mp hq2)).symm
          · simp [if_neg h1]
        · simp [if_neg h2]
    rw [hab, hba]; ring
  · push Not at houter
    obtain ⟨pos, hnoq1, hnoq2, hne⟩ := houter
    have zero_lhs : ∑ mid : Fin (2^n),
        (A (π qs₁ i) (π qs₁ mid) * if cc qs₁ i mid then (1:ℂ) else 0) *
        (B (π qs₂ mid) (π qs₂ l) * if cc qs₂ mid l then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro mid _
      by_cases h1 : cc qs₁ i mid
      · by_cases h2 : cc qs₂ mid l
        · exact False.elim (absurd ((h1 pos hnoq1).trans (h2 pos hnoq2)) hne)
        · simp [if_neg h2]
      · simp [if_neg h1]
    have zero_rhs : ∑ mid : Fin (2^n),
        (B (π qs₂ i) (π qs₂ mid) * if cc qs₂ i mid then (1:ℂ) else 0) *
        (A (π qs₁ mid) (π qs₁ l) * if cc qs₁ mid l then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro mid _
      by_cases h2 : cc qs₂ i mid
      · by_cases h1 : cc qs₁ mid l
        · exact False.elim (absurd ((h2 pos hnoq2).trans (h1 pos hnoq1)) hne)
        · simp [if_neg h1]
      · simp [if_neg h2]
    rw [zero_lhs]; exact zero_rhs.symm

end QLean

end
