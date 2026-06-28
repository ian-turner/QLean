import QLean

/-!
# Example: quantum Fourier transform circuit and its correctness

The QFT circuit on `n` qubits (Nielsen & Chuang §5.1, Fig 5.1), built from the library gate
primitives and the positional `embed`. Each layer processes one qubit: a Hadamard followed by a
cascade of controlled phase rotations `Rₖ` from the remaining qubits, addressed with `embed`. A
final `swapLayer` reverses the qubit order, faithful to the figure.

The construction recurses by peeling the **top** qubit (`Fin.last`, the MSB in the LSB index
convention), so the `j + 1 = (j) + 1` qubit-count arithmetic stays definitional:

  `qftCore (n+1) = (qftCore n ⊗ id₁) * qftStageTop n`

with the top qubit's H-plus-rotations stage acting first (rightmost), then the recursive QFT on
the low `n` qubits, which the stage leaves untouched.

Two results are proved:

* `isUnitary_qftCircuit` — well-formedness (every gate unitary ⇒ the whole circuit is unitary).
* `qftCore_correct` — the **product-form correctness** (N&C eq 5.4): on a basis input the QFT
  network (before the reversal swaps) produces the tensor of single-qubit states
  `❘0⟩ + e^{2πi · j/2^{m+1}} ❘1⟩` (up to `1/√2` each). The proof stays in the `QState` syntax layer
  (`≈`, `grw`/`gcongr`, the `QCircuit.*`/`QState.*` action lemmas); it drops to the matrix layer
  only for irreducible per-gate facts and the scalar/binary-fraction arithmetic. The qubit-reversal
  swap layer is not yet folded into the correctness statement.
-/

open scoped Matrix QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

-- ── Folding a list of gates into a sequential circuit preserves WF ────────────

/-- Prepending a list of well-formed gates onto a well-formed initial circuit is well-formed. -/
theorem wf_foldr_seq {n : ℕ} {α : Type*} (l : List α) (f : α → QCircuit n) (init : QCircuit n)
    (hinit : QCircuit.WF init) (hf : ∀ a ∈ l, QCircuit.WF (f a)) :
    QCircuit.WF (l.foldr (fun a acc => f a * acc) init) := by
  induction l with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact ⟨hf x (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun a ha => hf a (List.mem_cons.mpr (Or.inr ha)))⟩

-- ── One QFT layer: H on the top qubit, then controlled rotations ──────────────

/-- The controlled-rotation gate between the top qubit `Fin.last m` and a lower qubit `c`,
    embedded into `m+1` qubits: a controlled-`R_{m-c+1}`. -/
def qftCR (m : ℕ) (c : Fin m) : QCircuit (m + 1) :=
  QCircuit.embed (pairEmb (Fin.last m) c.castSucc (Fin.castSucc_lt_last c).ne')
        (.gate (controlled (Rk (m - c.val + 1))))

/-- The stage for the top qubit of an `(m+1)`-qubit register: a Hadamard on qubit `Fin.last m`
    (acting first, so it is the rightmost factor), then the controlled rotations `qftCR m c` from
    each lower qubit `c`. The controlled rotations are diagonal, so their order is immaterial. -/
def qftStageTop (m : ℕ) : QCircuit (m + 1) :=
  (List.finRange m).foldr (fun c acc => qftCR m c * acc)
    (QCircuit.embed (singleEmb (Fin.last m)) (.gate H))

theorem wf_qftStageTop (m : ℕ) : QCircuit.WF (qftStageTop m) := by
  unfold qftStageTop
  apply wf_foldr_seq
  · exact isUnitary_H
  · intro c _
    exact isUnitary_controlled (isUnitary_Rk _)

-- ── The QFT, without the qubit-reversal swaps ─────────────────────────────────

/-- The QFT network proper (no final swaps), recursing on the top qubit. The stage for the top
    qubit acts first; then the QFT on the low `n` qubits, which leaves the top qubit alone. -/
def qftCore : (n : ℕ) → QCircuit n
  | 0       => 1
  | (n + 1) => (qftCore n ⊗ (1 : QCircuit 1)) * qftStageTop n

theorem wf_qftCore (n : ℕ) : QCircuit.WF (qftCore n) := by
  induction n with
  | zero => exact wf_id
  | succ m ih =>
    show QCircuit.WF ((qftCore m ⊗ (1 : QCircuit 1)) * qftStageTop m)
    exact ⟨⟨ih, wf_id⟩, wf_qftStageTop m⟩

-- ── Qubit-reversal swap layer ─────────────────────────────────────────────────

/-- Reverse the qubit order: swap qubit `i` with qubit `n-1-i` for each `i < n/2`. -/
def swapLayer (n : ℕ) : QCircuit n :=
  (List.finRange (n / 2)).foldr
    (fun i acc =>
      QCircuit.embed
        (pairEmb (⟨i.val, by have := i.isLt; omega⟩ : Fin n)
                 (⟨n - 1 - i.val, by have := i.isLt; omega⟩ : Fin n)
          (by have hi := i.isLt; intro heq; rw [Fin.mk.injEq] at heq; omega))
        (.gate SWAP) * acc)
    1

theorem wf_swapLayer (n : ℕ) : QCircuit.WF (swapLayer n) := by
  unfold swapLayer
  apply wf_foldr_seq
  · exact wf_id
  · intro i _
    exact isUnitary_SWAP

-- ── The full QFT circuit ──────────────────────────────────────────────────────

/-- The quantum Fourier transform circuit on `n` qubits: the QFT network followed by the
    qubit-reversal swaps (which act last). -/
def qftCircuit (n : ℕ) : QCircuit n := swapLayer n * qftCore n

theorem wf_qftCircuit (n : ℕ) : QCircuit.WF (qftCircuit n) :=
  ⟨wf_swapLayer n, wf_qftCore n⟩

/-- The QFT circuit evaluates to a unitary matrix. -/
theorem isUnitary_qftCircuit (n : ℕ) : IsUnitary (QCircuit.eval (qftCircuit n)) :=
  QCircuit.eval_unitary _ (wf_qftCircuit n)

-- ════════════════════════════ Correctness ════════════════════════════════════
-- The semantic atoms: how one embedded gate acts on one basis ket, plus the scalar entries.

/-- The diagonal entry by which `qftCR m c` scales `ket x`. -/
def crEntry (m : ℕ) (c : Fin m) (x : Fin (2 ^ (m + 1))) : ℂ :=
  (controlled (Rk (m - c.val + 1)))
    (selectIdx (pairEmb (Fin.last m) c.castSucc (Fin.castSucc_lt_last c).ne') x)
    (selectIdx (pairEmb (Fin.last m) c.castSucc (Fin.castSucc_lt_last c).ne') x)

/-- `selectIdx` of a pair embedding reads its two bits (low = position `a`, high = position `b`). -/
theorem selectIdx_pairEmb_val {n} (a b : Fin n) (h : a ≠ b) (x : Fin (2 ^ n)) :
    (selectIdx (pairEmb a b h) x).val
      = (finFunctionFinEquiv.symm x a).val + 2 * (finFunctionFinEquiv.symm x b).val := by
  unfold selectIdx
  rw [finFunctionFinEquiv_apply_val, Fin.sum_univ_two]
  simp only [pairEmb_apply_zero, pairEmb_apply_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
             mul_one]
  ring

theorem controlled_Rk_diag (k : ℕ) (idx : Fin (2 ^ 2)) :
    (controlled (Rk k)) idx idx
      = if idx = 3 then Complex.exp (2 * Real.pi * Complex.I / (2:ℂ) ^ k) else 1 := by
  fin_cases idx <;> simp [controlled, Rk, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Bit `c` of the input `j` at the control position. -/
def jbit (m : ℕ) (c : Fin m) (j : Fin (2 ^ (m + 1))) : ℕ := (finFunctionFinEquiv.symm j c.castSucc).val

theorem jbit_lt (m : ℕ) (c : Fin m) (j : Fin (2 ^ (m + 1))) : jbit m c j < 2 := by
  have := (finFunctionFinEquiv.symm j c.castSucc).isLt; simpa [jbit] using this

theorem selectIdx_qftCR_merge (m : ℕ) (c : Fin m) (j : Fin (2 ^ (m + 1))) (s : Fin (2 ^ 1)) :
    (selectIdx (pairEmb (Fin.last m) c.castSucc (Fin.castSucc_lt_last c).ne')
        (mergeBits (singleEmb (Fin.last m)) j s)).val = s.val + 2 * jbit m c j := by
  rw [selectIdx_pairEmb_val]
  have h1 : finFunctionFinEquiv.symm (mergeBits (singleEmb (Fin.last m)) j s) (Fin.last m)
      = finFunctionFinEquiv.symm s 0 := by
    have := mergeBits_bit_mem (singleEmb (Fin.last m)) j s 0; simpa [singleEmb_apply] using this
  have h2 : finFunctionFinEquiv.symm (mergeBits (singleEmb (Fin.last m)) j s) c.castSucc
      = finFunctionFinEquiv.symm j c.castSucc :=
    mergeBits_bit_not_mem (singleEmb (Fin.last m)) j s c.castSucc
      (fun a => by rw [singleEmb_apply]; exact (Fin.castSucc_lt_last c).ne')
  rw [h1, h2, finFunctionFinEquiv_symm_apply_val]
  simp only [Fin.val_zero, pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt (show s.val < 2 by simpa using s.isLt)]; rfl

theorem crEntry_merge0 (m : ℕ) (c : Fin m) (j : Fin (2 ^ (m + 1))) :
    crEntry m c (mergeBits (singleEmb (Fin.last m)) j 0) = 1 := by
  unfold crEntry; rw [controlled_Rk_diag, if_neg]
  intro hcon
  have h3 := congrArg Fin.val hcon
  rw [selectIdx_qftCR_merge] at h3
  have e3 : (3 : Fin (2 ^ 2)).val = 3 := rfl
  have := jbit_lt m c j; rw [e3] at h3; simp only [Fin.val_zero, Nat.zero_add] at h3; omega

theorem crEntry_merge1 (m : ℕ) (c : Fin m) (j : Fin (2 ^ (m + 1))) :
    crEntry m c (mergeBits (singleEmb (Fin.last m)) j 1)
      = Complex.exp ((jbit m c j : ℂ) * (2 * Real.pi * Complex.I / (2:ℂ) ^ (m - c.val + 1))) := by
  unfold crEntry; rw [controlled_Rk_diag]
  have e3 : (3 : Fin (2 ^ 2)).val = 3 := rfl
  rcases (show jbit m c j = 0 ∨ jbit m c j = 1 by have := jbit_lt m c j; omega) with h0 | h1
  · rw [if_neg]
    · rw [h0]; simp
    · intro hcon; have h3 := congrArg Fin.val hcon; rw [selectIdx_qftCR_merge, e3] at h3
      simp only [Fin.val_one] at h3; rw [h0] at h3; omega
  · rw [if_pos]
    · rw [h1]; simp
    · apply Fin.ext; rw [selectIdx_qftCR_merge, e3]; simp only [Fin.val_one]; rw [h1]

-- ── Binary-fraction phase identity ────────────────────────────────────────────

/-- Digit reconstruction: an index is the sum of its bits times the place values. -/
theorem digit_recon (m : ℕ) (j : Fin (2 ^ (m + 1))) :
    (j : ℕ) = ∑ i : Fin (m + 1), (finFunctionFinEquiv.symm j i).val * 2 ^ (i : ℕ) := by
  conv_lhs => rw [show (j:ℕ) = (finFunctionFinEquiv (finFunctionFinEquiv.symm j)).val from by
                    rw [Equiv.apply_symm_apply]]
  rw [finFunctionFinEquiv_apply_val]

/-- The binary fraction `0.jₘ…j₀` equals `j / 2^{m+1}` (factored by `2πi` at the use site). -/
theorem qft_frac (m : ℕ) (j : Fin (2 ^ (m + 1))) :
    ((finFunctionFinEquiv.symm j (Fin.last m)).val : ℂ) / 2
      + (∑ c : Fin m, (jbit m c j : ℂ) / (2:ℂ) ^ (m - c.val + 1)) = (j.val : ℂ) / (2:ℂ) ^ (m + 1) := by
  have hcast : (j.val : ℂ) = (∑ c : Fin m, (jbit m c j : ℂ) * 2 ^ (c : ℕ))
      + ((finFunctionFinEquiv.symm j (Fin.last m)).val : ℂ) * 2 ^ m := by
    rw [digit_recon m j]; push_cast; rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, jbit]
  have e1 : ∀ c : Fin m, (jbit m c j : ℂ) / 2 ^ (m - c.val + 1) = (jbit m c j : ℂ) * 2 ^ (c : ℕ) / 2 ^ (m + 1) := by
    intro c
    have hc : (2:ℂ) ^ (m + 1) = 2 ^ (c : ℕ) * 2 ^ (m - c.val + 1) := by
      rw [← pow_add]; congr 1; have := c.isLt; omega
    rw [hc]; field_simp
  have e2 : ((finFunctionFinEquiv.symm j (Fin.last m)).val : ℂ) / 2
      = ((finFunctionFinEquiv.symm j (Fin.last m)).val : ℂ) * 2 ^ m / 2 ^ (m + 1) := by
    rw [show (2:ℂ) ^ (m + 1) = 2 ^ m * 2 from by rw [pow_succ]]; field_simp
  rw [hcast, add_div, Finset.sum_div, e2]; simp_rw [e1]; ring

-- ── Layer scalars: the rotation-product and the Hadamard entries ──────────────

/-- The product of the rotation phases over all controls is `exp` of the bit-weighted sum. -/
theorem prodMerge1 (m : ℕ) (j : Fin (2 ^ (m + 1))) :
    ((List.finRange m).map (fun c => crEntry m c (mergeBits (singleEmb (Fin.last m)) j 1))).prod
      = Complex.exp (∑ c : Fin m, (jbit m c j : ℂ) * (2 * Real.pi * Complex.I / (2:ℂ) ^ (m - c.val + 1))) := by
  rw [← Fin.prod_univ_def, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro c _; exact crEntry_merge1 m c j

theorem H_row0 (t : Fin (2 ^ 1)) : (H : QMatrix 1) 0 t = (Real.sqrt 2 : ℂ)⁻¹ := by
  fin_cases t <;> simp [H, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem H_row1 (t : Fin (2 ^ 1)) :
    (H : QMatrix 1) 1 t = (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / 2) := by
  fin_cases t
  · simp [H, Matrix.cons_val_zero, Matrix.cons_val_one]
  · show (H : QMatrix 1) 1 1 = (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((1 : Fin (2 ^ 1)).val : ℂ) / 2)
    rw [show (2 * (Real.pi:ℂ) * Complex.I * ((1 : Fin (2 ^ 1)).val : ℂ)) / 2 = (Real.pi:ℂ) * Complex.I from by
          simp only [Fin.val_one, Nat.cast_one]; ring, Complex.exp_pi_mul_I]
    simp [H, Matrix.cons_val_one]

theorem selectIdx_singleEmb_last_val (m : ℕ) (j : Fin (2 ^ (m + 1))) :
    (selectIdx (singleEmb (Fin.last m)) j).val = (finFunctionFinEquiv.symm j (Fin.last m)).val := by
  unfold selectIdx
  rw [finFunctionFinEquiv_apply_val]
  simp only [singleEmb, Function.Embedding.coeFn_mk, Finset.univ_unique, Finset.sum_singleton,
             Fin.default_eq_zero, Fin.val_zero, pow_zero, mul_one]

-- ── QState layer: the syntax-level action lemmas and the inductive proof ──────

variable {m : ℕ}

/-- Phase of the top output qubit for an `sz`-qubit register holding value `jv`: `e^{2πi·jv/2^sz}`. -/
def qftPhase (sz jv : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (jv : ℂ) / (2:ℂ) ^ sz)

/-- The QState lift of `qftCR_mul_ket`: an embedded controlled rotation scales a basis ket. -/
theorem qftCR_apply (c : Fin m) (x : Fin (2 ^ (m + 1))) :
    qftCR m c * (❘x⟩ : QState (m + 1)) ≈ crEntry m c x • ❘x⟩ := by
  unfold qftCR crEntry
  exact QCircuit.embed_diag_action _ (controlled_isDiag (Rk_isDiag _)) x

/-- The QState lift of `embed_single_mul_ket` for the Hadamard on the top qubit. -/
theorem embedH_apply (j : Fin (2 ^ (m + 1))) :
    QCircuit.embed (singleEmb (Fin.last m)) (.gate H) * (❘j⟩ : QState (m + 1))
      ≈ (H 0 (selectIdx (singleEmb (Fin.last m)) j)) • ❘mergeBits (singleEmb (Fin.last m)) j 0⟩
        + (H 1 (selectIdx (singleEmb (Fin.last m)) j)) • ❘mergeBits (singleEmb (Fin.last m)) j 1⟩ :=
  QCircuit.embed_single_action (singleEmb (Fin.last m)) H j

/-- The cascade, in the syntax layer: applying the foldr of controlled rotations onto the Hadamard
    keeps the input's low bits as a basis ket and threads the accumulated rotation phase onto the
    `❘1⟩` component of the top qubit. Proved by induction over the control list using only `QState`
    rewriting (`seq_action`, `apply_add`/`apply_smul`, the per-gate `qftCR_apply`, scalar algebra). -/
theorem stage_apply (j : Fin (2 ^ (m + 1))) (l : List (Fin m)) :
    (l.foldr (fun c acc => qftCR m c * acc)
        (QCircuit.embed (singleEmb (Fin.last m)) (.gate H))) * (❘j⟩ : QState (m + 1))
      ≈ (H 0 (selectIdx (singleEmb (Fin.last m)) j)) • ❘mergeBits (singleEmb (Fin.last m)) j 0⟩
        + ((H 1 (selectIdx (singleEmb (Fin.last m)) j))
            * (l.map (fun c => crEntry m c (mergeBits (singleEmb (Fin.last m)) j 1))).prod)
          • ❘mergeBits (singleEmb (Fin.last m)) j 1⟩ := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.prod_nil, mul_one]
    exact embedH_apply j
  | cons c cs ih =>
    have hfold : (c :: cs).foldr (fun c acc => qftCR m c * acc)
          (QCircuit.embed (singleEmb (Fin.last m)) (.gate H))
        = qftCR m c * (cs.foldr (fun c acc => qftCR m c * acc)
          (QCircuit.embed (singleEmb (Fin.last m)) (.gate H))) := rfl
    rw [hfold]
    grw [QCircuit.seq_action, ih, QCircuit.apply_add, QCircuit.apply_smul, QCircuit.apply_smul,
         qftCR_apply, qftCR_apply, crEntry_merge0]
    grw [QState.one_smul, QState.smul_smul]
    have hs : H 1 (selectIdx (singleEmb (Fin.last m)) j)
            * (List.map (fun c => crEntry m c (mergeBits (singleEmb (Fin.last m)) j 1)) cs).prod
            * crEntry m c (mergeBits (singleEmb (Fin.last m)) j 1)
        = H 1 (selectIdx (singleEmb (Fin.last m)) j)
            * (List.map (fun c => crEntry m c (mergeBits (singleEmb (Fin.last m)) j 1)) (c :: cs)).prod := by
      rw [List.map_cons, List.prod_cons]; ring
    rw [hs]

/-- The product-form single-qubit output state: `(❘0⟩ + e^{2πi·jv/2^sz} ❘1⟩)/√2`. -/
def qftQubitState (sz jv : ℕ) : QState 1 :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (❘(0 : Fin (2 ^ 1))⟩ + qftPhase sz jv • ❘(1 : Fin (2 ^ 1))⟩)

/-- The single-stage lemma: the top-qubit layer sends `❘j⟩` to the product state, separating the
    low qubits (still `❘j_low⟩`) from the top qubit's `qftQubitState`. -/
theorem qftStageTop_apply (j : Fin (2 ^ (m + 1))) :
    qftStageTop m * (❘j⟩ : QState (m + 1))
      ≈ ❘((tensorIndexEquiv m 1).symm j).1⟩ ⊗ qftQubitState (m + 1) j.val := by
  have key : (2 * Real.pi * Complex.I * ((finFunctionFinEquiv.symm j (Fin.last m)).val : ℂ) / 2
      + ∑ c : Fin m, (jbit m c j : ℂ) * (2 * Real.pi * Complex.I / (2:ℂ) ^ (m - c.val + 1)))
      = 2 * Real.pi * Complex.I * (((finFunctionFinEquiv.symm j (Fin.last m)).val : ℂ) / 2
        + ∑ c : Fin m, (jbit m c j : ℂ) / (2:ℂ) ^ (m - c.val + 1)) := by
    rw [mul_add, Finset.mul_sum]; congr 1
    · ring
    · apply Finset.sum_congr rfl; intro c _; ring
  have harg : (2 * Real.pi * Complex.I * ((finFunctionFinEquiv.symm j (Fin.last m)).val : ℂ) / 2
      + ∑ c : Fin m, (jbit m c j : ℂ) * (2 * Real.pi * Complex.I / (2:ℂ) ^ (m - c.val + 1)))
      = 2 * Real.pi * Complex.I * (j.val : ℂ) / (2:ℂ) ^ (m + 1) := by rw [key, qft_frac]; ring
  have hco : H 1 (selectIdx (singleEmb (Fin.last m)) j)
        * (List.map (fun c => crEntry m c (mergeBits (singleEmb (Fin.last m)) j 1)) (List.finRange m)).prod
      = (Real.sqrt 2 : ℂ)⁻¹ * qftPhase (m + 1) j.val := by
    rw [prodMerge1, H_row1, selectIdx_singleEmb_last_val, mul_assoc, ← Complex.exp_add, harg, qftPhase]
  refine (stage_apply j (List.finRange m)).trans ?_
  grw [H_row0, hco, mergeBits_singleEmb_last, mergeBits_singleEmb_last,
       QState.basis_tensor_split, QState.basis_tensor_split,
       ← QState.tensor_smul_right, ← QState.tensor_smul_right, ← QState.tensor_add_right]
  gcongr
  rw [qftQubitState]
  grw [QState.smul_add, QState.smul_smul]

/-- The product-form target state on `n` qubits: the tensor (low to high) of the per-qubit factors,
    each `qftQubitState` carrying the binary-fraction phase of `j`'s tail. -/
def qftProductState : (n : ℕ) → Fin (2 ^ n) → QState n
  | 0,       _ => ❘(0 : Fin (2 ^ 0))⟩
  | (n + 1), j => qftProductState n ((tensorIndexEquiv n 1).symm j).1 ⊗ qftQubitState (n + 1) j.val

/-- **Correctness of the QFT network** (Nielsen & Chuang eq 5.4), before the reversal swaps: on a
    computational basis input the QFT produces the product-form state. Clean induction in the syntax
    layer — `seq_action` to peel the stage, `qftStageTop_apply` for the single stage, then
    `par_action_tensor` + the inductive hypothesis on the low qubits. -/
theorem qftCore_correct : (n : ℕ) → (j : Fin (2 ^ n)) →
    qftCore n * (❘j⟩ : QState n) ≈ qftProductState n j
  | 0, j => by
    obtain rfl : j = 0 := by apply Fin.ext; have := j.isLt; simp only [pow_zero] at this; omega
    exact QCircuit.id_action _
  | (m + 1), j => by
    have ih := qftCore_correct m
    show (qftCore m ⊗ (1 : QCircuit 1)) * qftStageTop m * ❘j⟩
        ≈ qftProductState m ((tensorIndexEquiv m 1).symm j).1 ⊗ qftQubitState (m + 1) j.val
    grw [QCircuit.seq_action, qftStageTop_apply, QCircuit.par_action_tensor, ih, QCircuit.id_action]

end

end QLean.Examples
