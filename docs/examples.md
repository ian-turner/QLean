# Examples

Each file in `Examples/` demonstrates a self-contained quantum circuit result using the library. All examples import `QLean` and open the `QLean` namespace.

---

## `Examples/RzCNOT.lean` — Commutativity of Rz and CNOT

**Theorem:** `rz_commutes_cnot (θ : ℝ)` — `Rz(θ)` on qubit 0 (the CNOT control) commutes with CNOT.

**Technique:** Equational reasoning in the symbolic state layer, optimized for readability over brevity. By `Circuit.Equiv.basis_iff_tensor` it suffices to check both circuit orderings on every factored basis state `❘a⟩ ⊗ₛ ❘b⟩`. The Rz phase `φ` is kept abstract (`RzGate_basis`) — its value is irrelevant to commutativity. A helper `rz_phase` shows `Rz ⊗ 1` phases any basis tensor with control `❘a⟩` by `φ`; then two `calc` blocks reduce each ordering to the same phased state `φ • (❘a⟩ ⊗ₛ ❘a+b⟩)`, joined by transitivity. Each `calc` step is one of two kinds: an *action lemma* that reshapes the expression (`Circuit.seq_action`, `Circuit.par_action_tensor`, `Circuit.apply_smul`, `QState.smul_tensor_left`), or a `gcongr` descent into a context that rewrites a sub-state. (`simp` cannot drive this chain: `≈` is `eval`-equality, not syntactic equality, so rewrites only reach the outermost `eval`, not nested sub-states; the `@[gcongr]`-tagged congruence lemmas recover the congruence half. See `docs/lean-api.md`.)

**Key lemmas/tactics used:** `Circuit.Equiv.basis_iff_tensor`, `RzGate_basis`, `CNOTGate_basis_tensor`, `Circuit.seq_action`, `Circuit.par_action_tensor`, `Circuit.apply_smul`, `QState.smul_tensor_left`, and `gcongr` (via the `@[gcongr]` congruence lemmas)

---

## `Examples/HadamardTransform.lean` — n-qubit Hadamard transform

**Definitions:**
- `hadamardTransform n : Circuit n` — H applied in parallel to every qubit; defined recursively as `hadamardTransform n ⊗ HGate`
- `plusState : QState 1` — the symbolic single-qubit uniform superposition `|+⟩ = (❘0⟩ + ❘1⟩)/√2` (the RHS of `HGate_bit0`)
- `uniformSuperState n : QState n` — the symbolic n-qubit uniform superposition; a tensor power of `plusState`, one `|+⟩` per qubit

**Theorem:** `hadamardTransform_prepares (n : ℕ)` — `hadamardTransform n * ❘0⟩ ≈ uniformSuperState n`.

**Technique:** Symbolic equational reasoning in the `QState` layer, like `rz_commutes_cnot`. Induction on `n` whose inductive step is a single `grw` chain (`rw` modulo `≈`, descending under the tensor/apply congruences): split the input `❘0⟩ ≈ ❘0⟩ ⊗ₛ ❘0⟩` (`QState.ket_zero_tensor`), act componentwise (`Circuit.par_action_tensor`), apply the inductive hypothesis to the low `n` qubits and `HGate_bit0` to the high qubit, landing on `uniformSuperState n ⊗ₛ plusState = uniformSuperState (n+1)`. This replaces the earlier index-chasing through `tensorIndexEquiv`/`kron_mul_ket` and a concrete `1/√(2^n)` amplitude vector.

**Key lemmas/tactics used:** `QState.ket_zero_tensor`, `Circuit.par_action_tensor`, `HGate_bit0`, `Circuit.id_action`, `grw`

---

## `Examples/GHZ.lean` — Chain GHZ circuit

**Definitions:**
- `ghzCircuit n : Circuit (n+1)` — H on qubit 0, then `CNOT(k, k+1)` for `k = 0..n−1`; each step entangles one more qubit
- `ghzState n : QVector (n+1)` — `(ket 0 + ket (allOnes n)) / √2`; equal superposition of all-zeros and all-ones

**Theorems:**
- `wf_ghzCircuit n` — the GHZ circuit is well-formed (all leaves unitary); proved by induction using `simp` and `isUnitary_H` / `isUnitary_CNOT`
- `ghzCircuit_prepares n` — the circuit prepares `ghzState n` from `ket 0`

**Technique:** The main proof is by induction on `n`. The inductive step uses `kron_mul_ket` to split the CNOT layer, then `tensorState_add_left` and linearity to distribute over the superposition, identifies the all-ones index via `allOnes_low_reindex` and `cnot_result_eq_allOnes`, and closes with `CNOT_ket_zero'` / `CNOT_ket_one'`.

**Key lemmas used:** `kron_mul_ket`, `ket_tensorState`, `tensorState_add_left`, `CNOT_ket_pair`, index arithmetic on `tensorIndexEquiv`
