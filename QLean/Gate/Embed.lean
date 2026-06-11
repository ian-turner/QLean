import QLean.Gate.Standard
import Mathlib.Logic.Equiv.Fin.Basic

open Classical

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

-- Shorthand for the projection and complement condition
private abbrev π {n k : ℕ} (qs : Fin k ↪ Fin n) (x : Fin (2^n)) : Fin (2^k) :=
  finFunctionFinEquiv (finFunctionFinEquiv.symm x ∘ qs)

private abbrev cc {n k : ℕ} (qs : Fin k ↪ Fin n) (a b : Fin (2^n)) : Prop :=
  ∀ l : Fin n, (∀ m : Fin k, qs m ≠ l) → finFunctionFinEquiv.symm a l = finFunctionFinEquiv.symm b l

-- gateAt in compact notation
@[simp] private lemma gateAt_eq {n k : ℕ} (qs : Fin k ↪ Fin n) (U : QMatrix k) (i j : Fin (2^n)) :
    gateAt qs U i j = U (π qs i) (π qs j) * if cc qs i j then 1 else 0 := rfl

private lemma cc_symm {n k : ℕ} (qs : Fin k ↪ Fin n) (a b : Fin (2^n)) :
    cc qs a b ↔ cc qs b a :=
  ⟨fun h l hl => (h l hl).symm, fun h l hl => (h l hl).symm⟩

private lemma cc_trans {n k : ℕ} (qs : Fin k ↪ Fin n) {a b c : Fin (2^n)} :
    cc qs a b → cc qs b c → cc qs a c :=
  fun hab hbc l hl => (hab l hl).trans (hbc l hl)

private lemma cc_iff_of_ab {n k : ℕ} (qs : Fin k ↪ Fin n) {a b : Fin (2^n)} (l : Fin (2^n))
    (hab : cc qs a b) : cc qs a l ↔ cc qs l b :=
  ⟨fun h => cc_trans qs ((cc_symm qs a l).mp h) hab,
   fun h => cc_trans qs hab ((cc_symm qs l b).mp h)⟩

-- ── mergeBits helper ──────────────────────────────────────────────────────────

private def mergeBits {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) : Fin (2^n) :=
  finFunctionFinEquiv (fun l =>
    if h : ∃ a : Fin k, qs a = l then s h.choose else c l)

-- Selected bits round-trip
private lemma mb_sel {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) (m : Fin k) :
    finFunctionFinEquiv.symm (mergeBits qs c s) (qs m) = s m := by
  simp only [mergeBits, Equiv.symm_apply_apply]
  rw [dif_pos ⟨m, rfl⟩]
  exact congr_arg s (qs.injective (Exists.choose_spec ⟨m, rfl⟩))

-- Complement bits round-trip
private lemma mb_comp {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) (l : Fin n) (hl : ∀ a : Fin k, qs a ≠ l) :
    finFunctionFinEquiv.symm (mergeBits qs c s) l = c l := by
  simp only [mergeBits, Equiv.symm_apply_apply]
  exact dif_neg (fun ⟨a, ha⟩ => hl a ha)

-- π (mergeBits qs c s) = finFunctionFinEquiv s
private lemma π_mb {n k : ℕ} (qs : Fin k ↪ Fin n)
    (c : Fin n → Fin 2) (s : Fin k → Fin 2) :
    π qs (mergeBits qs c s) = finFunctionFinEquiv s := by
  simp only [π]
  suffices h : finFunctionFinEquiv.symm (mergeBits qs c s) ∘ qs = s by rw [h]
  funext m; exact mb_sel qs c s m

-- Full round-trip
private lemma mb_rt {n k : ℕ} (qs : Fin k ↪ Fin n) (i : Fin (2^n)) :
    mergeBits qs (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm i ∘ qs) = i := by
  apply finFunctionFinEquiv.symm.injective
  funext l
  simp only [mergeBits, Equiv.symm_apply_apply]
  split_ifs with h
  · exact congr_arg (finFunctionFinEquiv.symm i) h.choose_spec
  · rfl

-- cc holds for mergeBits
private lemma cc_mb {n k : ℕ} (qs : Fin k ↪ Fin n) (i : Fin (2^n)) (s : Fin k → Fin 2) :
    cc qs i (mergeBits qs (finFunctionFinEquiv.symm i) s) :=
  fun l hl => (mb_comp qs _ s l hl).symm

-- mergeBits undoes π when cc holds
private lemma mb_π {n k : ℕ} (qs : Fin k ↪ Fin n) (i l : Fin (2^n)) (hcl : cc qs i l) :
    mergeBits qs (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm (π qs l)) = l := by
  apply finFunctionFinEquiv.symm.injective
  funext pos
  simp only [mergeBits, π, Equiv.symm_apply_apply]
  split_ifs with hq
  · exact congr_arg (finFunctionFinEquiv.symm l) hq.choose_spec
  · exact hcl pos (fun a ha => hq ⟨a, ha⟩)

-- ── gateAt_conjTranspose ──────────────────────────────────────────────────────

theorem gateAt_conjTranspose {n k : ℕ} (qs : Fin k ↪ Fin n) (U : QMatrix k) :
    (gateAt qs U)ᴴ = gateAt qs Uᴴ := by
  ext i j
  by_cases h : cc qs i j
  · have h' : cc qs j i := (cc_symm qs i j).mp h
    simp only [gateAt_eq, Matrix.conjTranspose_apply, h, h', if_true, mul_one,
               Matrix.conjTranspose_apply]
  · have h' : ¬cc qs j i := fun hji => h ((cc_symm qs j i).mp hji)
    simp only [gateAt_eq, Matrix.conjTranspose_apply, h, h', if_false, mul_zero,
               map_zero]

-- ── gateAt_one ───────────────────────────────────────────────────────────────

theorem gateAt_one {n k : ℕ} (qs : Fin k ↪ Fin n) : gateAt qs (1 : QMatrix k) = 1 := by
  ext i j
  simp only [gateAt_eq, Matrix.one_apply]
  by_cases hcc : cc qs i j
  · simp only [hcc, if_true, mul_one]
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
    · simp only [hproj, if_false, ite_eq_right_iff]
      intro hij; exact absurd (congr_arg (π qs) hij) hproj
  · simp only [hcc, if_false, mul_zero, eq_comm]
    have hne : i ≠ j := fun hij => hcc (hij ▸ fun _ _ => rfl)
    simp [hne]

-- ── gateAt_mul ───────────────────────────────────────────────────────────────

theorem gateAt_mul {n k : ℕ} (qs : Fin k ↪ Fin n) (A B : QMatrix k) :
    gateAt qs (A * B) = gateAt qs A * gateAt qs B := by
  ext i j
  simp only [gateAt_eq, Matrix.mul_apply]
  by_cases hcc : cc qs i j
  · -- i and j agree on complement: reduce to sum over Fin (2^k)
    simp only [hcc, if_true, mul_one]
    -- Simplify the combined indicator in each term
    have hind : ∀ l : Fin (2^n),
        (A (π qs i) (π qs l) * (if cc qs i l then (1:ℂ) else 0)) *
        (B (π qs l) (π qs j) * (if cc qs l j then 1 else 0)) =
        A (π qs i) (π qs l) * B (π qs l) (π qs j) * (if cc qs i l then 1 else 0) := fun l => by
      have heq : (if cc qs l j then (1:ℂ) else 0) = if cc qs i l then 1 else 0 := by
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((cc_iff_of_ab qs l hcc).mp h2) h1 |>.elim
        · exact absurd ((cc_iff_of_ab qs l hcc).mpr h1) h2 |>.elim
        · rfl
      rw [heq]; ring
    simp only [hind]
    -- Reduce to filter sum
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    -- Biject Fin (2^k) → filter via m ↦ mergeBits qs (symm i) (symm m)
    let emb := fun m : Fin (2^k) =>
      mergeBits qs (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm m)
    have hπ : ∀ m : Fin (2^k), π qs (emb m) = m := fun m => by
      simp only [emb, π_mb]; simp
    symm
    apply Finset.sum_nbij emb
    · intro m _; simp only [Finset.mem_filter, Finset.mem_univ, true_and, emb]; exact cc_mb qs i _
    · intro m₁ _ m₂ _ h
      have := congr_arg (π qs) h; rwa [hπ, hπ] at this
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact ⟨π qs l, Finset.mem_univ _, mb_π qs i l hl⟩
    · intro m _
      simp only [emb, hπ]
  · -- i and j disagree: both sides are 0
    simp only [hcc, if_false, mul_zero]
    symm
    apply Finset.sum_eq_zero; intro l _
    simp only [gateAt_eq]
    by_cases hil : cc qs i l
    · have hjl : ¬cc qs l j := fun hlj => hcc (cc_trans qs hil hlj)
      simp [hjl]
    · simp [hil]

-- ── gateAt_unitary ───────────────────────────────────────────────────────────

theorem gateAt_unitary {n k : ℕ} (qs : Fin k ↪ Fin n) {U : QMatrix k}
    (hu : IsUnitary U) : IsUnitary (gateAt qs U) := by
  unfold IsUnitary
  rw [gateAt_conjTranspose, ← gateAt_mul, hu, gateAt_one]

-- ── Embedding helpers ─────────────────────────────────────────────────────────

private def singletonEmbed {n : ℕ} (i : Fin n) : Fin 1 ↪ Fin n :=
  ⟨Fin.cases i Fin.elim0, by intro a b _; fin_cases a <;> fin_cases b <;> simp⟩

private def pairEmbed {n : ℕ} (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : Fin 2 ↪ Fin n :=
  ⟨![ctrl, tgt], by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]⟩

-- ── Convenience wrappers ──────────────────────────────────────────────────────

def hadamardAt {n : ℕ} (i : Fin n) : QMatrix n := gateAt (singletonEmbed i) H
def cnotAt {n : ℕ} (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : QMatrix n :=
  gateAt (pairEmbed ctrl tgt h) CNOT
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

private noncomputable def commMid {n j k : ℕ}
    (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n) (i l : Fin (2^n)) : Fin (2^n) :=
  finFunctionFinEquiv (fun pos =>
    if ∃ a : Fin j, qs₁ a = pos then finFunctionFinEquiv.symm l pos
    else finFunctionFinEquiv.symm i pos)

theorem gateAt_comm_disjoint {n j k : ℕ} (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n)
    (hdisj : Disjoint (Set.range qs₁) (Set.range qs₂))
    (A : QMatrix j) (B : QMatrix k) :
    gateAt qs₁ A * gateAt qs₂ B = gateAt qs₂ B * gateAt qs₁ A := by
  have hd : ∀ (a : Fin j) (b : Fin k), qs₁ a ≠ qs₂ b := fun a b hab =>
    Set.disjoint_left.mp hdisj (Set.mem_range_self a) ⟨b, hab.symm⟩
  ext i l
  simp only [Matrix.mul_apply, gateAt_eq]
  -- Whether outer bits (complement of both ranges) agree between i and l
  by_cases houter : ∀ pos : Fin n,
      (∀ a : Fin j, qs₁ a ≠ pos) → (∀ b : Fin k, qs₂ b ≠ pos) →
      finFunctionFinEquiv.symm i pos = finFunctionFinEquiv.symm l pos
  · -- Outer bits agree: each sum has exactly one non-zero term
    have val_eq : A (π qs₁ i) (π qs₁ l) * B (π qs₂ i) (π qs₂ l) =
                  A (π qs₁ i) (π qs₁ l) * B (π qs₂ i) (π qs₂ l) := rfl
    -- For A*B order: unique surviving mid = commMid qs₁ qs₂ i l
    set mid₁₂ := commMid qs₁ qs₂ i l with hmid₁₂_def
    have hcc₁_i : cc qs₁ i mid₁₂ := by
      intro pos hpos
      simp only [mid₁₂, commMid, Equiv.symm_apply_apply, dif_neg (fun ⟨a, ha⟩ => hpos a ha)]
    have hcc₂_l : cc qs₂ mid₁₂ l := by
      intro pos hpos
      simp only [mid₁₂, commMid, Equiv.symm_apply_apply]
      by_cases hq1 : ∃ a : Fin j, qs₁ a = pos
      · rw [dif_pos hq1]
      · rw [dif_neg hq1]
        exact houter pos (fun a ha => hq1 ⟨a, ha⟩) hpos
    have hπ₁_l : π qs₁ mid₁₂ = π qs₁ l := by
      simp only [π, mid₁₂, commMid, Equiv.symm_apply_apply]
      congr 1; funext m; simp [Function.comp, dif_pos (⟨m, rfl⟩ : ∃ a : Fin j, qs₁ a = qs₁ m)]
    have hπ₂_i : π qs₂ mid₁₂ = π qs₂ i := by
      simp only [π, mid₁₂, commMid, Equiv.symm_apply_apply]
      congr 1; funext m
      simp [Function.comp, dif_neg (fun ⟨a, ha⟩ => hd a m ha)]
    rw [Finset.sum_eq_single mid₁₂ _ (fun h => absurd (Finset.mem_univ _) h)]
    · rw [hπ₁_l, hπ₂_i, if_pos hcc₁_i, if_pos hcc₂_l]; ring
    · intro mid _ hmid
      by_cases h1 : cc qs₁ i mid
      · by_cases h2 : cc qs₂ mid l
        · exfalso; apply hmid
          apply finFunctionFinEquiv.symm.injective; funext pos
          simp only [mid₁₂, commMid, Equiv.symm_apply_apply]
          by_cases hq1 : ∃ a : Fin j, qs₁ a = pos
          · rw [dif_pos hq1]
            obtain ⟨a, rfl⟩ := hq1
            exact (h2 (qs₁ a) (fun b hb => hd a b hb)).symm
          · rw [dif_neg hq1]; exact (h1 pos (fun a ha => hq1 ⟨a, ha⟩)).symm
        · simp [if_neg h2]
      · simp [if_neg h1]
    -- For B*A order: unique surviving mid = commMid qs₂ qs₁ l i
    set mid₂₁ := commMid qs₂ qs₁ l i with hmid₂₁_def
    have hcc₂_i : cc qs₂ i mid₂₁ := by
      intro pos hpos
      simp only [mid₂₁, commMid, Equiv.symm_apply_apply, dif_neg (fun ⟨b, hb⟩ => hpos b hb)]
    have hcc₁_l : cc qs₁ mid₂₁ l := by
      intro pos hpos
      simp only [mid₂₁, commMid, Equiv.symm_apply_apply]
      by_cases hq2 : ∃ b : Fin k, qs₂ b = pos
      · rw [dif_pos hq2]
        obtain ⟨b, rfl⟩ := hq2
        exact houter (qs₂ b) (fun a ha => hd a b ha) (fun b' hb' => hpos b' hb') |>.symm
      · rw [dif_neg hq2]; exact houter pos hpos (fun b hb => hq2 ⟨b, hb⟩)
    have hπ₂_i' : π qs₂ mid₂₁ = π qs₂ i := by
      simp only [π, mid₂₁, commMid, Equiv.symm_apply_apply]
      congr 1; funext m; simp [Function.comp, dif_pos (⟨m, rfl⟩ : ∃ b : Fin k, qs₂ b = qs₂ m)]
    have hπ₁_l' : π qs₁ mid₂₁ = π qs₁ l := by
      simp only [π, mid₂₁, commMid, Equiv.symm_apply_apply]
      congr 1; funext m
      simp [Function.comp, dif_neg (fun ⟨b, hb⟩ => hd m b hb.symm)]
    rw [Finset.sum_eq_single mid₂₁ _ (fun h => absurd (Finset.mem_univ _) h)]
    · rw [hπ₂_i', hπ₁_l', if_pos hcc₂_i, if_pos hcc₁_l]; ring
    · intro mid _ hmid
      by_cases h2 : cc qs₂ i mid
      · by_cases h1 : cc qs₁ mid l
        · exfalso; apply hmid
          apply finFunctionFinEquiv.symm.injective; funext pos
          simp only [mid₂₁, commMid, Equiv.symm_apply_apply]
          by_cases hq2 : ∃ b : Fin k, qs₂ b = pos
          · rw [dif_pos hq2]
            obtain ⟨b, rfl⟩ := hq2
            exact (h1 (qs₂ b) (fun a ha => hd a b ha.symm)).symm
          · rw [dif_neg hq2]; exact (h2 pos (fun b hb => hq2 ⟨b, hb⟩)).symm
        · simp [if_neg h1]
      · simp [if_neg h2]
  · -- Outer bits disagree: both sums vanish
    push_neg at houter
    obtain ⟨pos, hnoq1, hnoq2, hne⟩ := houter
    have zero_lhs : ∑ mid : Fin (2^n),
        A (π qs₁ i) (π qs₁ mid) * (if cc qs₁ i mid then (1:ℂ) else 0) *
        (B (π qs₂ mid) (π qs₂ l) * (if cc qs₂ mid l then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro mid _
      by_cases h1 : cc qs₁ i mid
      · by_cases h2 : cc qs₂ mid l
        · exact absurd ((h1 pos hnoq1).trans (h2 pos hnoq2)) hne |>.elim
        · simp [if_neg h2]
      · simp [if_neg h1]
    have zero_rhs : ∑ mid : Fin (2^n),
        B (π qs₂ i) (π qs₂ mid) * (if cc qs₂ i mid then (1:ℂ) else 0) *
        (A (π qs₁ mid) (π qs₁ l) * (if cc qs₁ mid l then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro mid _
      by_cases h2 : cc qs₂ i mid
      · by_cases h1 : cc qs₁ mid l
        · exact absurd ((h2 pos hnoq2).trans (h1 pos hnoq1)) hne |>.elim
        · simp [if_neg h1]
      · simp [if_neg h2]
    have lhs_eq : ∑ mid : Fin (2^n),
        A (π qs₁ i) (π qs₁ mid) * (if cc qs₁ i mid then (1:ℂ) else 0) *
        (B (π qs₂ mid) (π qs₂ l) * (if cc qs₂ mid l then 1 else 0)) =
        ∑ mid : Fin (2^n), gateAt qs₁ A i mid * gateAt qs₂ B mid l := by
      simp [gateAt_eq, mul_comm, mul_assoc]
    have rhs_eq : ∑ mid : Fin (2^n),
        B (π qs₂ i) (π qs₂ mid) * (if cc qs₂ i mid then (1:ℂ) else 0) *
        (A (π qs₁ mid) (π qs₁ l) * (if cc qs₁ mid l then 1 else 0)) =
        ∑ mid : Fin (2^n), gateAt qs₂ B i mid * gateAt qs₁ A mid l := by
      simp [gateAt_eq, mul_comm, mul_assoc]
    rw [← lhs_eq, zero_lhs, ← rhs_eq, zero_rhs]

end QLean

end
