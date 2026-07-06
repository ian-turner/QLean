# Examples

Each file in `Examples/` demonstrates a self-contained quantum circuit result using the library. All examples import `QLean` and open the `QLean` namespace.

---

## `Examples/RzPlus.lean` — Rz rotation angles add

**Theorem:** `rz_plus (θ φ : ℝ)` — `RzGate φ * RzGate θ ≈ RzGate (θ + φ)`: running `Rz θ` then `Rz φ` (the rightmost factor acts first) is a single Z-rotation by `θ + φ`.

**Technique:** The one example proved directly at the matrix level rather than in the `QState` layer: unfold `QCircuit.Equiv`/`QCircuit.eval`/`Rz` with `simp`, then `ring_nf` and `Complex.exp_add` merge the diagonal phase factors entrywise. A minimal template for gate-fusion identities where both sides are literally the same `2×2` matrix.

**Key lemmas/tactics used:** `QCircuit.Equiv`, `QCircuit.eval`, `Rz`, `Complex.exp_add`, `simp`, `ring_nf`

---

## `Examples/RzCNOT.lean` — Commutativity of Rz and CNOT

**Theorem:** `rz_commutes_cnot (θ : ℝ)` — `Rz(θ)` on qubit 0 (the CNOT control) commutes with CNOT.

**Technique:** Equational reasoning in the symbolic state layer, optimized for readability over brevity. By `QCircuit.Equiv.basis_iff_tensor` it suffices to check both circuit orderings on every factored basis state `❘a⟩ ⊗ ❘b⟩`. The Rz phase `φ` is kept abstract (`RzGate_basis`) — its value is irrelevant to commutativity. A helper `rz_phase` shows `Rz ⊗ 1` phases any basis tensor with control `❘a⟩` by `φ`; then two `calc` blocks reduce each ordering to the same phased state `φ • (❘a⟩ ⊗ ❘a+b⟩)`, joined by transitivity. Each `calc` step is one of two kinds: an *action lemma* that reshapes the expression (`QCircuit.seq_action`, `QCircuit.par_action_tensor`, `QCircuit.apply_smul`, `QState.smul_tensor_left`), or a `gcongr` descent into a context that rewrites a sub-state. (`simp` cannot drive this chain: `≈` is `eval`-equality, not syntactic equality, so rewrites only reach the outermost `eval`, not nested sub-states; the `@[gcongr]`-tagged congruence lemmas recover the congruence half. See `docs/lean-api.md`.)

**Key lemmas/tactics used:** `QCircuit.Equiv.basis_iff_tensor`, `RzGate_basis`, `CNOTGate_basis_tensor`, `QCircuit.seq_action`, `QCircuit.par_action_tensor`, `QCircuit.apply_smul`, `QState.smul_tensor_left`, and `gcongr` (via the `@[gcongr]` congruence lemmas)

---

## `Examples/HadamardTransform.lean` — n-qubit Hadamard transform

**Definitions:**
- `hadamardTransform n : QCircuit n` — H applied in parallel to every qubit; defined recursively as `hadamardTransform n ⊗ HGate`
- `plusState : QState 1` — the symbolic single-qubit uniform superposition `|+⟩ = (❘0⟩ + ❘1⟩)/√2` (the RHS of `HGate_bit0`)
- `uniformSuperState n : QState n` — the symbolic n-qubit uniform superposition; a tensor power of `plusState`, one `|+⟩` per qubit

**Theorem:** `hadamardTransform_prepares (n : ℕ)` — `hadamardTransform n * ❘0⟩ ≈ uniformSuperState n`.

**Technique:** Symbolic equational reasoning in the `QState` layer, like `rz_commutes_cnot`. Induction on `n` whose inductive step is a single `grw` chain (`rw` modulo `≈`, descending under the tensor/apply congruences): split the input `❘0⟩ ≈ ❘0⟩ ⊗ ❘0⟩` (`QState.ket_zero_tensor`), act componentwise (`QCircuit.par_action_tensor`), apply the inductive hypothesis to the low `n` qubits and `HGate_bit0` to the high qubit, landing on `uniformSuperState n ⊗ plusState = uniformSuperState (n+1)`. This replaces the earlier index-chasing through `tensorIndexEquiv` and a concrete `1/√(2^n)` amplitude vector.

**Key lemmas/tactics used:** `QState.ket_zero_tensor`, `QCircuit.par_action_tensor`, `HGate_bit0`, `QCircuit.id_action`, `grw`

---

## `Examples/BellState.lean` — Bell state preparation

**Definitions:**
- `bellCircuit : QCircuit (1 + 1)` — `CNOTGate * (HGate ⊗ (1 : QCircuit 1))`: a Hadamard on qubit 0 (the low qubit) followed by a CNOT with control qubit 0 and target qubit 1 (the rightmost factor acts first). Typed at `1 + 1` (not `2`) so the `QState.ket_zero_tensor 1 1` split matches the goal syntactically.
- `bellState : QState (1 + 1)` — the symbolic Bell state `|Φ⁺⟩ = (❘00⟩ + ❘11⟩)/√2`. Unlike `uniformSuperState`, it is *entangled*: it does not factor as a tensor product.

**Theorem:** `bellCircuit_prepares` — `bellCircuit * ❘00⟩ ≈ bellState`.

**Technique:** Symbolic equational reasoning in the `QState` layer, like the other examples, as a single `grw` chain. `QCircuit.seq_action` reorders to "apply `HGate ⊗ 1`, then `CNOTGate`"; the input splits as `❘0⟩ ≈ ❘0⟩ ⊗ ❘0⟩` (`QState.ket_zero_tensor`) and the parallel gate acts componentwise (`QCircuit.par_action_tensor`), with `HGate_bit0` turning the low qubit into `(❘0⟩ + ❘1⟩)/√2` and `QCircuit.id_action` leaving the high qubit. The scalar and sum are then pushed out through the tensor and the remaining `CNOTGate` (`QState.smul_tensor_left`, `QState.add_tensor_left`, `QCircuit.apply_smul`, `QCircuit.apply_add`) so the CNOT lands on each basis tensor, where `CNOTGate_basis_tensor` flips the target to give `(❘00⟩ + ❘11⟩)/√2`. The chain leaves the targets as `❘0 + 0⟩`/`❘1 + 0⟩`, which are `❘0⟩`/`❘1⟩` definitionally, so a final `rfl` (via the `@[refl]` lemma `QState.Equiv.refl`) closes the goal. This is the only example that distributes a circuit over a superposition.

**Key lemmas/tactics used:** `QCircuit.seq_action`, `QState.ket_zero_tensor`, `QCircuit.par_action_tensor`, `HGate_bit0`, `QCircuit.id_action`, `QState.smul_tensor_left`, `QState.add_tensor_left`, `QCircuit.apply_smul`, `QCircuit.apply_add`, `CNOTGate_basis_tensor`, `grw`, `rfl`

---

## `Examples/GHZState.lean` — GHZ state preparation

**Definitions:**
- `ghzCircuit n : QCircuit (n + 1)` — the GHZ preparation circuit, indexed by the number of CNOTs `n`: `ghzCircuit 0 = HGate`, and `ghzCircuit (n+1) = ((1 : QCircuit n) ⊗ CNOTGate) * (ghzCircuit n ⊗ (1 : QCircuit 1))` — each step adds one qubit and one CNOT entangling the new top qubit with the previous one. `ghzCircuit 1` is exactly the Bell circuit.
- `ghzState n : QState (n + 1)` — the symbolic GHZ state `(|0…0⟩ + |1…1⟩)/√2`, an equal superposition of the all-zeros ket `❘0⟩` and the all-ones ket `❘allOnes (n+1)⟩`. Maximally entangled; the normalization is always `1/√2` (only ever two terms).

**Theorems:** `wf_ghzCircuit n` — the circuit is well-formed; `ghzCircuit_prepares n` — `ghzCircuit n * ❘0⟩ ≈ ghzState n`.

**Technique:** Symbolic equational reasoning in the `QState` layer, by induction on `n`. The base case is a single Hadamard (`HGate_bit0`, with `allOnes 1 = 1`). The inductive step is the first example to require **tensor re-association**: GHZ's CNOT cascade acts on overlapping pairs of qubits in *different* tensor bracketings, so between the inductive hypothesis (which leaves `ghzState n ⊗ ❘0⟩`) and the final `1 ⊗ CNOTGate`, each superposition term must be re-bracketed via `QState.tensor_assoc` to expose the previous top qubit and the new qubit as an adjacent pair. This is the structural step the Hadamard transform (pure tensor power) and Bell (two qubits, single bracketing) never needed. The all-ones ket is split with the new `QState.allOnes_succ` lemma, mirroring `QState.ket_zero_tensor` for the all-zeros ket. After the CNOT copies the control bit onto the new qubit (`CNOTGate_basis_tensor`, extending the all-zeros and all-ones runs), a final `gcongr` matches the result against `ghzState (n+1)` by re-expanding its two basis kets.

**Key lemmas/tactics used:** `QState.ket_zero_tensor`, `QState.allOnes_succ`, `QState.tensor_assoc`, `QState.smul_tensor_left`, `QState.add_tensor_left`, `QCircuit.seq_action`, `QCircuit.par_action_tensor`, `QCircuit.id_action`, `QCircuit.apply_smul`, `QCircuit.apply_add`, `HGate_bit0`, `CNOTGate_basis_tensor`, `grw`, `gcongr`, `rfl`

---

## `Examples/QFT.lean` — Quantum Fourier transform circuit

**Definitions** (Nielsen & Chuang §5.1, Fig 5.1; all in `QLean.Examples`):
- `qftStageTop n : QCircuit (n+1)` — one QFT layer: a Hadamard on qubit `Fin.last n`, then a controlled-`R_{n-c+1}` between that qubit and each lower qubit `c`. A `foldr` of gates positioned with the first-class `QCircuit.embed` constructor over `List.finRange n`; the rotations are diagonal, so their order is immaterial.
- `qftCore n : QCircuit n` — the QFT network without the final swaps, recursing by peeling the **top** qubit: `qftCore (n+1) = (qftCore n ⊗ id₁) * qftStageTop n`. Peeling `Fin.last` (the MSB in the LSB index convention) keeps the `(n)+1` qubit-count arithmetic definitional. The top-qubit stage acts first; the recursive QFT on the low `n` qubits leaves the top qubit alone.
- `swapLayer n : QCircuit n` — qubit-reversal: an embedded `SWAP` between qubit `i` and `n-1-i` for each `i < n/2`.
- `qftCircuit n : QCircuit n` — `swapLayer n * qftCore n`: the QFT network followed by the reversal swaps (which act last).
- `qftQubitState sz jv : QState 1` — the per-qubit product factor `(❘0⟩ + e^{2πi·jv/2^sz} ❘1⟩)/√2`; `qftProductState n j : QState n` — the n-fold tensor of these (N&C eq 5.4).

- `qftProgram n : Program n` — the **serializable** form of `qftCircuit n` in the flat `Program` IR (`qftCRProg`/`qftStageTopProg`/`qftCoreProg`/`swapLayerProg`): the same named gates and placements, but as data that compiles to OpenQASM. The recursive core's parallel step `qftCore n ⊗ id₁` is re-addressed onto the low `n` qubits with `Program.relabel (lowEmb n 1)`, since `Program` has no `par`.

**Theorems:** `wf_qftCircuit n`/`isUnitary_qftCircuit n` — the circuit is well-formed / unitary; **`qftCore_correct n j`** — `qftCore n * ❘j⟩ ≈ qftProductState n j`, the product-form correctness of the QFT network (before the reversal swaps); **`denote_qftProgram n`** — `(qftProgram n).denote ≈ qftCircuit n`, the acid test that the serializable program denotes to exactly the verified circuit (with `isUnitary_qftProgram n` following directly from `Program.denote_unitary`).

**Technique (well-formedness):** Exercises the positional `embed` *constructor* rather than the structural `par`/`⊗`: each layer's H and controlled rotations live on non-adjacent qubits, which `par` cannot express. Every leaf is `QCircuit.embed qs (gate U)`, so well-formedness is structural — `WF (embed qs (gate U))` reduces to `IsUnitary U` (`isUnitary_H`/`isUnitary_controlled (isUnitary_Rk _)`/`isUnitary_SWAP`) with no `embed_unitary` at the use site; `wf_foldr_seq` (from `Circuit/Semantics.lean`) carries the WF induction over each layer's gate list.

**Technique (correctness):** Kept **entirely** in the `QState` syntax layer (see the GHZ/Bell pattern) — no matrix entry appears in the example. Every gate-specific fact enters through the two phase-form action lemmas in `Gate/StateActions.lean`: `embed_H_action` (H splits a ket, the `❘1⟩` branch carrying the sign `(-1)ᵇ` as a phase) and `embed_controlled_Rk_action` (the embedded controlled rotation scales by `e^{2πi/2ᵏ}` when both addressed bits are set). Those wrap the gate-agnostic `QCircuit.embed_single_action`/`embed_diag_action` and the matrix-entry atoms `H_row0`/`H_row1`/`controlled_Rk_diag` (now in `Gate/Standard.lean`), so the example bottoms out only at index-arithmetic (`selectIdx_qftCR_merge`, `selectIdx_singleEmb_last_val`) and the scalar/binary-fraction arithmetic (`qft_frac` via `digit_recon`, `prodMerge1` via `Complex.exp_sum`). The per-stage actions are stated as symbolic phases: `qftCR_merge0` (fixes the top-bit-`0` branch) / `qftCR_merge1` (`crPhase`), with `hPhase` the Hadamard's contribution. Everything structural is symbolic: `stage_apply` inducts over the control list threading the rotation phase with `seq_action`/`apply_add`/`apply_smul` + `QState.smul_smul`; `qftStageTop_apply` combines `hPhase · prodMerge1` into the single output phase `qftPhase` via `qft_frac`, then repackages into a tensor with `basis_tensor_split` + `tensor_smul_right`/`tensor_add_right`; and `qftCore_correct` is a clean induction with `seq_action` → `qftStageTop_apply` → `par_action_tensor` → IH → `id_action`. The phase works out to exactly `e^{2πi·j/2^{m+1}}` (the binary fraction `0.jₘ…j₀`). The qubit-reversal swap layer is not yet folded into the correctness statement.

**Technique (acid test):** `qftProgram` mirrors `qftCircuit` constructor-for-constructor with `Program` primitives, so each piece denotes *definitionally* to its circuit counterpart — `denote_qftStageTopProg`/`denote_swapLayerProg` are `Program.denote_foldr_seq` (push `denote` through the gate `foldr`) then `rfl` (each `prim g`'s denotation reduces to the matching `embed … (gate g.matrix)`). The only non-`rfl` step is the core recursion: `denote_qftCoreProg` inducts, rewriting the program's `relabel (lowEmb n 1)` to an `embed` with `Program.denote_relabel` and matching it against `qftCore`'s `⊗ id₁` via `QCircuit.par_as_embed` + `embed_id` + `seq_id_right` (all under `grw`, using the `@[gcongr]` `embed_congr`). `denote_qftProgram` then assembles the swap and core halves. The proof never touches a matrix entry — it runs entirely on the circuit-level `embed` algebra.

**Key lemmas/tactics used:** `QCircuit.embed`/`singleEmb`/`pairEmb`/`Rk`/`controlled`, `embed_H_action`/`embed_controlled_Rk_action` (phase-form actions in `Gate/StateActions.lean`), `mergeBits_singleEmb_last`, `QCircuit.seq_action`/`apply_add`/`apply_smul`/`par_action_tensor`/`id_action`, `QState.one_smul`/`smul_smul`/`smul_add`/`basis_tensor_split`/`tensor_smul_right`/`tensor_add_right`, `Complex.exp_sum`/`exp_pi_mul_I`, `grw`/`gcongr`, `wf_foldr_seq`, `QCircuit.eval_unitary`
