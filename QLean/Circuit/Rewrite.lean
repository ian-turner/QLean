import QLean.Circuit.Semantics
import QLean.Basic.Hilbert

namespace QLean

open Circuit

noncomputable section

-- ── Circuit.Equiv ─────────────────────────────────────────────────────────────

/-- Two circuits are equivalent if they evaluate to the same unitary. -/
def Circuit.Equiv (c₁ c₂ : Circuit n) : Prop := eval c₁ = eval c₂

@[refl]  theorem Circuit.Equiv.refl  (c : Circuit n) : Circuit.Equiv c c := rfl
@[symm]  theorem Circuit.Equiv.symm  {c₁ c₂ : Circuit n} : Circuit.Equiv c₁ c₂ → Circuit.Equiv c₂ c₁ :=
  Eq.symm
@[trans] theorem Circuit.Equiv.trans {c₁ c₂ c₃ : Circuit n} :
    Circuit.Equiv c₁ c₂ → Circuit.Equiv c₂ c₃ → Circuit.Equiv c₁ c₃ := Eq.trans

instance : Trans (@Circuit.Equiv n) (@Circuit.Equiv n) (@Circuit.Equiv n) :=
  ⟨Circuit.Equiv.trans⟩

-- ── Congruence lemmas ─────────────────────────────────────────────────────────

/-- Equivalent components yield equivalent sequential circuits. -/
theorem Circuit.Equiv.seq_congr {c₁ c₁' c₂ c₂' : Circuit n}
    (h₁ : Circuit.Equiv c₁ c₁') (h₂ : Circuit.Equiv c₂ c₂') :
    Circuit.Equiv (.seq c₁ c₂) (.seq c₁' c₂') := by
  unfold Circuit.Equiv at *; simp only [eval_seq]; rw [h₁, h₂]

/-- Equivalent components yield equivalent parallel circuits. -/
theorem Circuit.Equiv.par_congr {c₁ c₁' : Circuit j} {c₂ c₂' : Circuit k}
    (h₁ : Circuit.Equiv c₁ c₁') (h₂ : Circuit.Equiv c₂ c₂') :
    Circuit.Equiv (.par c₁ c₂) (.par c₁' c₂') := by
  unfold Circuit.Equiv at *; simp only [eval_par]; rw [h₁, h₂]

-- ── Basic rewrite rules ───────────────────────────────────────────────────────

/-- `id` is a left identity for sequential composition. -/
theorem seq_id_left (c : Circuit n) : Circuit.Equiv (.seq .id c) c := by
  simp [Circuit.Equiv]

/-- `id` is a right identity for sequential composition. -/
theorem seq_id_right (c : Circuit n) : Circuit.Equiv (.seq c .id) c := by
  simp [Circuit.Equiv]

/-- Sequential composition is associative. -/
theorem seq_assoc (c₁ c₂ c₃ : Circuit n) :
    Circuit.Equiv (.seq (.seq c₁ c₂) c₃) (.seq c₁ (.seq c₂ c₃)) := by
  simp [Circuit.Equiv, mul_assoc]

-- ── par_assoc ─────────────────────────────────────────────────────────────────

/-- Parallel composition is associative up to `castN` and `Circuit.Equiv`. -/
theorem par_assoc (c₁ : Circuit j) (c₂ : Circuit k) (c₃ : Circuit l) :
    Circuit.Equiv
      (Circuit.castN (Nat.add_assoc j k l) (.par (.par c₁ c₂) c₃))
      (.par c₁ (.par c₂ c₃)) := by
  simp only [Circuit.Equiv, eval_castN, eval_par]
  exact kronQMatrix_assoc (eval c₁) (eval c₂) (eval c₃)

-- ── Basis characterization ───────────────────────────────────────────────────

private lemma mul_ket_apply {n : ℕ} (M : QMatrix n) (i r : Fin (2^n)) :
    (M * ket i) r 0 = M r i := by
  simp [Matrix.mul_apply, ket_apply, mul_ite, Finset.sum_ite_eq', Finset.mem_univ]

/-- Two circuits are equivalent iff they act identically on every computational basis state. -/
theorem Circuit.Equiv.basis_iff {n : ℕ} (c₁ c₂ : Circuit n) :
    Circuit.Equiv c₁ c₂ ↔ ∀ i : Fin (2^n), eval c₁ * ket i = eval c₂ * ket i := by
  unfold Circuit.Equiv
  constructor
  · intro h i; rw [h]
  · intro h
    ext r c
    simpa [mul_ket_apply] using congr_fun (congr_fun (h c) r) 0

-- ── Interchange law ──────────────────────────────────────────────────────────

/-- Parallel composition distributes over sequential composition:
    running two sequences in parallel equals sequencing two parallel steps. -/
theorem interchange_law {j k : ℕ} (a b : Circuit j) (c d : Circuit k) :
    Circuit.Equiv (.par (.seq a b) (.seq c d)) (.seq (.par a c) (.par b d)) := by
  simp [Circuit.Equiv, ← kronQMatrix_mul]

end

end QLean
