# Examples

Each file in `Examples/` demonstrates a self-contained quantum circuit result using the library. All examples import `QLean` and open the `QLean` namespace.

---

## `Examples/RzCNOT.lean` — Commutativity of Rz and CNOT

**Theorem:** `rz_commutes_cnot (θ : ℝ)` — `Rz(θ)` on qubit 0 (the CNOT control) commutes with CNOT.

**Technique:** Basis-state reasoning via `Circuit.Equiv.basis_iff`. The proof decomposes a 2-qubit index into a tensor-product pair, applies `kron_mul_ket` to split the Kronecker action, and uses `Rz_ket_diag` (Rz is diagonal, so it produces a scalar phase on a basis ket) together with `CNOT_tensorState_smul_ket` (CNOT commutes with a scalar on the control).

**Key lemmas used:** `Circuit.Equiv.basis_iff`, `kron_mul_ket`, `Rz_ket_diag`, `CNOT_tensorState_smul_ket`

---

## `Examples/HadamardTransform.lean` — n-qubit Hadamard transform

**Definitions:**
- `hadamardTransform n : Circuit n` — H applied in parallel to every qubit; defined recursively as `hadamardTransform n + HGate`
- `uniformSuper n : QState n` — uniform superposition with amplitude `1/√(2^n)` at every basis state

**Theorem:** `hadamardTransform_prepares (n : ℕ)` — the circuit prepares `uniformSuper n` from `ket 0`.

**Technique:** Induction on `n`. The base case is a direct computation for `H * ket 0`. The inductive step rewrites `ket 0 : Fin (2^(n+1))` as `ket (tensorIndexEquiv n 1 ⟨0, 0⟩)`, applies `kron_mul_ket` to split the Kronecker action, uses the inductive hypothesis on the low qubits and `H_ket_zero` on the high qubit, and closes with `tensorState_uniformSuper`.

**Key lemmas used:** `kron_mul_ket`, `tensorState_uniformSuper`, `H_ket_zero`

---

## `Examples/GHZ.lean` — Chain GHZ circuit

**Definitions:**
- `ghzCircuit n : Circuit (n+1)` — H on qubit 0, then `CNOT(k, k+1)` for `k = 0..n−1`; each step entangles one more qubit
- `ghzState n : QState (n+1)` — `(ket 0 + ket (allOnes n)) / √2`; equal superposition of all-zeros and all-ones

**Theorems:**
- `wf_ghzCircuit n` — the GHZ circuit is well-formed (all leaves unitary); proved by induction using `simp` and `isUnitary_H` / `isUnitary_CNOT`
- `ghzCircuit_prepares n` — the circuit prepares `ghzState n` from `ket 0`

**Technique:** The main proof is by induction on `n`. The inductive step uses `kron_mul_ket` to split the CNOT layer, then `tensorState_add_left` and linearity to distribute over the superposition, identifies the all-ones index via `allOnes_low_reindex` and `cnot_result_eq_allOnes`, and closes with `CNOT_ket_zero'` / `CNOT_ket_one'`.

**Key lemmas used:** `kron_mul_ket`, `ket_tensorState`, `tensorState_add_left`, `CNOT_ket_pair`, index arithmetic on `tensorIndexEquiv`

---

## `Examples/QFT.lean` — Quantum Fourier Transform

**Definitions:**
- `qftState n j : QState n` — the DFT of the delta function at `j`: amplitude at `k` is `e^{2πijk/2^n} / √(2^n)`
- `qftMatrix n : QMatrix n` — the DFT unitary; entry `(k, j)` is `e^{2πijk/N} / √N` where `N = 2^n`
- `QFTGate n : Circuit n` — the QFT as a single circuit gate

**Theorems:**
- `isUnitary_qftMatrix n` — the DFT matrix is unitary; proved via the discrete orthogonality of roots of unity (`qft_phase_sum`)
- `QFTGate_maps_ket n j` — QFT applied to `ket j` produces `qftState n j`
- `qftMatrix_one_eq_H` — `qftMatrix 1 = H`; the 1-qubit QFT is the Hadamard gate

**Technique:** Unitarity uses `qft_phase_sum`, which evaluates `∑ k, exp(2πi(i-j)k/N)` to `N` on the diagonal and `0` off-diagonal via the geometric series formula (`geom_sum_mul`) and a non-vanishing lemma for roots of unity. The `qftMatrix_one_eq_H` identity is checked by `fin_cases` on the 2×2 matrix.

**Key lemmas used:** `qft_phase_sum`, `exp_frac_pow`, `exp_frac_ne_one`, `geom_sum_mul`
