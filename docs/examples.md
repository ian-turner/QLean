# Examples

Each file in `Examples/` demonstrates a self-contained quantum circuit result using the library. All examples import `QLean` and open the `QLean` namespace.

---

## `Examples/RzCNOT.lean` — Commutativity of Rz and CNOT

**Theorem:** `rz_commutes_cnot (θ : ℝ)` — `Rz(θ)` on qubit 0 (the CNOT control) commutes with CNOT.

**Technique:** Equational reasoning in the symbolic state layer, optimized for readability over brevity. By `Circuit.Equiv.basis_iff_tensor` it suffices to check both circuit orderings on every factored basis state `❘a⟩ ⊗ ❘b⟩`. The Rz phase `φ` is kept abstract (`RzGate_basis`) — its value is irrelevant to commutativity. A helper `rz_phase` shows `Rz ⊗ 1` phases any basis tensor with control `❘a⟩` by `φ`; then two `calc` blocks reduce each ordering to the same phased state `φ • (❘a⟩ ⊗ ❘a+b⟩)`, joined by transitivity. Each `calc` step is one of two kinds: an *action lemma* that reshapes the expression (`Circuit.seq_action`, `Circuit.par_action_tensor`, `Circuit.apply_smul`, `QState.smul_tensor_left`), or a `gcongr` descent into a context that rewrites a sub-state. (`simp` cannot drive this chain: `≈` is `eval`-equality, not syntactic equality, so rewrites only reach the outermost `eval`, not nested sub-states; the `@[gcongr]`-tagged congruence lemmas recover the congruence half. See `docs/lean-api.md`.)

**Key lemmas/tactics used:** `Circuit.Equiv.basis_iff_tensor`, `RzGate_basis`, `CNOTGate_basis_tensor`, `Circuit.seq_action`, `Circuit.par_action_tensor`, `Circuit.apply_smul`, `QState.smul_tensor_left`, and `gcongr` (via the `@[gcongr]` congruence lemmas)

---

## `Examples/HadamardTransform.lean` — n-qubit Hadamard transform

**Definitions:**
- `hadamardTransform n : Circuit n` — H applied in parallel to every qubit; defined recursively as `hadamardTransform n ⊗ HGate`
- `plusState : QState 1` — the symbolic single-qubit uniform superposition `|+⟩ = (❘0⟩ + ❘1⟩)/√2` (the RHS of `HGate_bit0`)
- `uniformSuperState n : QState n` — the symbolic n-qubit uniform superposition; a tensor power of `plusState`, one `|+⟩` per qubit

**Theorem:** `hadamardTransform_prepares (n : ℕ)` — `hadamardTransform n * ❘0⟩ ≈ uniformSuperState n`.

**Technique:** Symbolic equational reasoning in the `QState` layer, like `rz_commutes_cnot`. Induction on `n` whose inductive step is a single `grw` chain (`rw` modulo `≈`, descending under the tensor/apply congruences): split the input `❘0⟩ ≈ ❘0⟩ ⊗ ❘0⟩` (`QState.ket_zero_tensor`), act componentwise (`Circuit.par_action_tensor`), apply the inductive hypothesis to the low `n` qubits and `HGate_bit0` to the high qubit, landing on `uniformSuperState n ⊗ plusState = uniformSuperState (n+1)`. This replaces the earlier index-chasing through `tensorIndexEquiv`/`kron_mul_ket` and a concrete `1/√(2^n)` amplitude vector.

**Key lemmas/tactics used:** `QState.ket_zero_tensor`, `Circuit.par_action_tensor`, `HGate_bit0`, `Circuit.id_action`, `grw`

---

## `Examples/BellState.lean` — Bell state preparation

**Definitions:**
- `bellCircuit : Circuit (1 + 1)` — `(HGate ⊗ (1 : Circuit 1)) * CNOTGate`: a Hadamard on qubit 0 (the low qubit) followed by a CNOT with control qubit 0 and target qubit 1. Typed at `1 + 1` (not `2`) so the `QState.ket_zero_tensor 1 1` split matches the goal syntactically.
- `bellState : QState (1 + 1)` — the symbolic Bell state `|Φ⁺⟩ = (❘00⟩ + ❘11⟩)/√2`. Unlike `uniformSuperState`, it is *entangled*: it does not factor as a tensor product.

**Theorem:** `bellCircuit_prepares` — `bellCircuit * ❘00⟩ ≈ bellState`.

**Technique:** Symbolic equational reasoning in the `QState` layer, like the other examples, as a single `grw` chain. `Circuit.seq_action` reorders to "apply `HGate ⊗ 1`, then `CNOTGate`"; the input splits as `❘0⟩ ≈ ❘0⟩ ⊗ ❘0⟩` (`QState.ket_zero_tensor`) and the parallel gate acts componentwise (`Circuit.par_action_tensor`), with `HGate_bit0` turning the low qubit into `(❘0⟩ + ❘1⟩)/√2` and `Circuit.id_action` leaving the high qubit. The scalar and sum are then pushed out through the tensor and the remaining `CNOTGate` (`QState.smul_tensor_left`, `QState.add_tensor_left`, `Circuit.apply_smul`, `Circuit.apply_add`) so the CNOT lands on each basis tensor, where `CNOTGate_basis_tensor` flips the target to give `(❘00⟩ + ❘11⟩)/√2`. The chain leaves the targets as `❘0 + 0⟩`/`❘1 + 0⟩`, which are `❘0⟩`/`❘1⟩` definitionally, so a final `rfl` (via the `@[refl]` lemma `QState.Equiv.refl`) closes the goal. This is the only example that distributes a circuit over a superposition.

**Key lemmas/tactics used:** `Circuit.seq_action`, `QState.ket_zero_tensor`, `Circuit.par_action_tensor`, `HGate_bit0`, `Circuit.id_action`, `QState.smul_tensor_left`, `QState.add_tensor_left`, `Circuit.apply_smul`, `Circuit.apply_add`, `CNOTGate_basis_tensor`, `grw`, `rfl`
