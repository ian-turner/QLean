import QLean

namespace QLean.Examples

open QLean

noncomputable section

-- ── GHZ circuit (chain structure) ─────────────────────────────────────────────

/-- Chain GHZ circuit on n+1 qubits: H on qubit 0, then CNOT(k, k+1) for k = 0..n−1.
    Each step entangles one more qubit by applying CNOT to the last pair. -/
def ghzCircuit : (n : ℕ) → Circuit (n + 1)
  | 0     => HGate
  | n + 1 => (ghzCircuit n + (1 : Circuit 1)) * ((1 : Circuit n) + CNOTGate)

-- ── Well-formedness ────────────────────────────────────────────────────────────

/-- Every gate in the GHZ circuit is unitary. -/
theorem wf_ghzCircuit (n : ℕ) : Circuit.WF (ghzCircuit n) := by
  induction n with
  | zero      => simp [ghzCircuit, isUnitary_H]
  | succ n ih => simp [ghzCircuit, ih, isUnitary_CNOT]

-- ── GHZ state ─────────────────────────────────────────────────────────────────

/-- Index of the all-ones basis state on n+1 qubits. -/
private def allOnes (n : ℕ) : Fin (2 ^ (n + 1)) :=
  ⟨2 ^ (n + 1) - 1, by
    have h : 0 < (2 : ℕ) ^ (n + 1) := by positivity
    omega⟩

/-- GHZ state: equal superposition of |0...0⟩ and |1...1⟩ on n+1 qubits. -/
def ghzState (n : ℕ) : QState (n + 1) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (ket 0 + ket (allOnes n))

-- ── Helper lemmas ──────────────────────────────────────────────────────────────

-- The value of tensorIndexEquiv ⟨a, b⟩ is a.val + b.val * 2^j.
private lemma tensorIndexEquiv_val (j k : ℕ) (a : Fin (2 ^ j)) (b : Fin (2 ^ k)) :
    (tensorIndexEquiv j k ⟨a, b⟩).val = a.val + b.val * 2 ^ j := by
  have ha := tensorIndexEquiv_symm_fst_val j k (tensorIndexEquiv j k ⟨a, b⟩)
  have hb := tensorIndexEquiv_symm_snd_val j k (tensorIndexEquiv j k ⟨a, b⟩)
  simp only [Equiv.symm_apply_apply] at ha hb
  set x := (tensorIndexEquiv j k ⟨a, b⟩).val
  -- ha : a.val = x % 2^j,  hb : b.val = x / 2^j
  calc x = 2 ^ j * (x / 2 ^ j) + x % 2 ^ j := (Nat.div_add_mod x (2 ^ j)).symm
    _ = 2 ^ j * b.val + a.val := by rw [← hb, ← ha]
    _ = a.val + b.val * 2 ^ j := by ring

-- tensorState distributes over addition in the first argument.
private lemma tensorState_add_left {j k : ℕ} (ψ₁ ψ₂ : QState j) (φ : QState k) :
    tensorState (ψ₁ + ψ₂) φ = tensorState ψ₁ φ + tensorState ψ₂ φ := by
  funext i c; fin_cases c
  simp [tensorState_apply, add_mul]

-- Matrix multiplication commutes with complex scalar multiplication.
private lemma matrix_mul_smul {n : ℕ} (A : QMatrix n) (c : ℂ) (v : QState n) :
    A * (c • v) = c • (A * v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ k : Fin (2 ^ n), A i k * (c * v k j) = c * (A i k * v k j)
            from fun k => by ring]
  rw [← Finset.mul_sum]

-- All-ones index restricted to the n low bits.
private def allOnesPred (n : ℕ) : Fin (2 ^ n) :=
  ⟨2 ^ n - 1, by
    have h : 0 < (2 : ℕ) ^ n := by positivity
    omega⟩

-- tensorIndexEquiv ⟨0, 0⟩ = 0.
private lemma tensorIndexEquiv_zero_zero' (j k : ℕ) :
    tensorIndexEquiv j k ⟨(0 : Fin (2 ^ j)), (0 : Fin (2 ^ k))⟩ = 0 := by
  apply Fin.ext
  rw [tensorIndexEquiv_val]
  simp

-- The all-ones-on-low-(n+1)-bits index equals the (n, 2)-split ⟨allOnesPred n, 1⟩.
private lemma allOnes_low_reindex (n : ℕ) :
    tensorIndexEquiv (n + 1) 1 ⟨allOnes n, (0 : Fin 2)⟩ =
    tensorIndexEquiv n 2 ⟨allOnesPred n, (1 : Fin 4)⟩ := by
  apply Fin.ext
  rw [tensorIndexEquiv_val, tensorIndexEquiv_val]
  have h0 : (0 : Fin 2).val = 0 := rfl
  have h1 : (1 : Fin 4).val = 1 := rfl
  have hA : (allOnes n).val = 2 ^ (n + 1) - 1 := rfl
  have hB : (allOnesPred n).val = 2 ^ n - 1 := rfl
  rw [h0, h1, hA, hB, pow_succ (2 : ℕ)]
  have hpos : 0 < (2 : ℕ) ^ n := by positivity
  omega

-- After CNOT, the (n, 2)-split ⟨allOnesPred n, 3⟩ equals allOnes (n+1).
private lemma cnot_result_eq_allOnes (n : ℕ) :
    tensorIndexEquiv n 2 ⟨allOnesPred n, (3 : Fin 4)⟩ = allOnes (n + 1) := by
  apply Fin.ext
  rw [tensorIndexEquiv_val]
  have h3 : (3 : Fin 4).val = 3 := rfl
  have hB : (allOnesPred n).val = 2 ^ n - 1 := rfl
  have hC : (allOnes (n + 1)).val = 2 ^ (n + 2) - 1 := rfl
  rw [h3, hB, hC, show n + 2 = n + 1 + 1 from rfl, pow_succ (2:ℕ), pow_succ (2:ℕ)]
  have hpos : 0 < (2 : ℕ) ^ n := by positivity
  omega

private lemma CNOT_ket_zero' : CNOT * ket (0 : Fin 4) = ket 0 := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  fin_cases r <;>
    simp [Matrix.mul_apply, CNOT, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma CNOT_ket_one' : CNOT * ket (1 : Fin 4) = ket 3 := by
  ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
  fin_cases r <;>
    simp [Matrix.mul_apply, CNOT, ket_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

-- ── Main theorem ───────────────────────────────────────────────────────────────

/-- The (n+1)-qubit chain GHZ circuit prepares the GHZ state (|0...0⟩ + |1...1⟩)/√2.
    Proof by induction: at each step CNOT propagates the superposition to one more qubit. -/
theorem ghzCircuit_prepares (n : ℕ) : (ghzCircuit n).prepares (ghzState n) := by
  simp only [Circuit.maps_iff]
  induction n with
  | zero =>
    simp only [ghzCircuit, eval_gate]
    ext r c; obtain rfl : c = 0 := Subsingleton.elim c 0
    fin_cases r <;>
      simp [H, ghzState, allOnes, ket_apply, Matrix.mul_apply, Matrix.smul_apply,
            Matrix.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, pow_succ, pow_zero]
  | succ n ih =>
    simp only [ghzCircuit, eval_seq, eval_par, eval_id, eval_gate]
    rw [Matrix.mul_assoc]
    -- Step 1: first factor acts on |0...0⟩; close with the inductive hypothesis.
    conv_lhs =>
      rw [show (0 : Fin (2 ^ (n + 2))) = tensorIndexEquiv (n + 1) 1 ⟨0, 0⟩ from
            (tensorIndexEquiv_zero_zero' (n + 1) 1).symm]
      rw [kron_mul_ket, Matrix.one_mul, ih]
    -- Goal: kron 1 CNOT * tensorState (ghzState n) (ket 0) = ghzState (n+1)
    -- Step 2: unfold ghzState n and use bilinearity to get a sum of tensor states.
    simp only [ghzState]
    rw [tensorState_smul_left, matrix_mul_smul, tensorState_add_left, Matrix.mul_add]
    -- Step 3: express each tensorState as a ket at the (n+1, 1) split index.
    rw [ket_tensorState, ket_tensorState]
    -- Step 4: reindex from (n+1, 1) to (n, 2) split for kron_mul_ket.
    conv_lhs =>
      rw [show tensorIndexEquiv (n + 1) 1 ⟨(0 : Fin (2 ^ (n + 1))), (0 : Fin 2)⟩ =
              tensorIndexEquiv n 2 ⟨(0 : Fin (2 ^ n)), (0 : Fin (2 ^ 2))⟩ from by
            apply Fin.ext; rw [tensorIndexEquiv_val, tensorIndexEquiv_val]; simp]
      rw [allOnes_low_reindex]
    -- Step 5: apply CNOT to each ket via kron_mul_ket.
    have hk0 : kron (1 : QMatrix n) CNOT *
        ket (tensorIndexEquiv n 2 ⟨(0 : Fin (2 ^ n)), (0 : Fin (2 ^ 2))⟩) =
        tensorState ((1 : QMatrix n) * ket 0) (CNOT * ket 0) :=
      kron_mul_ket _ _ _ _
    have hk1 : kron (1 : QMatrix n) CNOT *
        ket (tensorIndexEquiv n 2 ⟨allOnesPred n, (1 : Fin (2 ^ 2))⟩) =
        tensorState ((1 : QMatrix n) * ket (allOnesPred n)) (CNOT * ket 1) :=
      kron_mul_ket _ _ _ _
    rw [hk0, hk1, Matrix.one_mul, Matrix.one_mul, CNOT_ket_zero', CNOT_ket_one']
    -- Step 6: collapse tensor states back to kets and identify the all-ones index.
    rw [ket_tensorState, ket_tensorState, tensorIndexEquiv_zero_zero', cnot_result_eq_allOnes]

end

end QLean.Examples
