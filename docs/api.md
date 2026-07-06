# API Reference

Per-module reference. Each section describes one source file: its purpose, key definitions, and public interface. For design rationale see [architecture.md](architecture.md).

---

## `Basic/Matrix.lean`

Foundational types and unitarity algebra.

**Key definitions:**
- `QMatrix n` — `abbrev` for `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`; the type of all n-qubit gates
- `IsUnitary U` — `U * Uᴴ = 1`; the single-condition unitarity predicate

**Key theorems:**
- `IsUnitary.conj_mul` — `IsUnitary U → Uᴴ * U = 1` (derived via Dedekind-finiteness)
- `IsUnitary.mul` — product of unitaries is unitary

---

## `Basic/Tensor.lean`

The Kronecker product lifted to `QMatrix`.

**Key definitions:**
- `tensorIndexEquiv j k : Fin (2^j) × Fin (2^k) ≃ Fin (2^(j+k))` — the index bridge, LSB-first
- `kron A B : QMatrix (j+k)` — reindexed Kronecker product; this is `eval`'s semantics for `par`

**Key theorems:**
- `kron_mul` — mixed-product: `kron (A*C) (B*D) = kron A B * kron C D`
- `kron_conjTranspose` — `(kron A B)ᴴ = kron Aᴴ Bᴴ`
- `kron_one_one` — `kron 1 1 = 1`
- `kron_assoc` — associativity of `kron` up to `reindex` (used in `QCircuit.par_assoc`)
- `IsUnitary.kron` — `IsUnitary A → IsUnitary B → IsUnitary (kron A B)`
- `tensorIndexEquiv_symm_fst_val`, `tensorIndexEquiv_symm_snd_val` — decompose an index into its low and high parts
- `tensorIndexEquiv_apply_val` — forward value `(tensorIndexEquiv j k p).val = p.1 + p.2 * 2^j` (companion to the symm decomposition)

---

## `Basic/Embed.lean`

Positional embedding: lifting a `k`-qubit gate onto `k` chosen qubits of an `n`-qubit
system. Unlike `par`/`⊗`, the target qubits may be non-adjacent or reordered (e.g. a CNOT
between qubits `0` and `2`). The construction is point-wise on matrix entries — no
permutation matrices and no `n - k` subtraction.

**Key definitions:**
- `selectIdx qs i : Fin (2^k)` — the `Fin (2^k)` index read off the qubits `qs : Fin k ↪ Fin n` selects from `i` (LSB convention, via `finFunctionFinEquiv`)
- `AgreeOff qs i j : Prop` — `i` and `j` carry the same bits on every qubit *outside* `range qs`; has `.refl`/`.symm`/`.trans`
- `embed qs U : QMatrix n` — `U` acting on the qubits selected by `qs`, identity elsewhere; entry `(i,j)` is `U (selectIdx qs i) (selectIdx qs j)` gated by `AgreeOff qs i j`
- `mergeBits qs i s : Fin (2^n)` — index carrying bits `s : Fin (2^k)` on the selected qubits and agreeing with `i` elsewhere; a one-sided inverse to `selectIdx`. The address-reconstruction primitive the state-action lemmas (`Basic/EmbedState.lean`) are phrased with
- `singleEmb t : Fin 1 ↪ Fin n` — embed at a single qubit `t`; `@[simp]` lemma `singleEmb_apply`
- `pairEmb a b (h : a ≠ b) : Fin 2 ↪ Fin n` — embed at two distinct qubits (`a` = gate-qubit `0`, `b` = gate-qubit `1`); `@[simp]` lemmas `pairEmb_apply_zero/one`. The addressing for embedded single- and two-qubit gates (e.g. the QFT layers)
- `lowEmb j k : Fin j ↪ Fin (j+k)`, `highEmb j k : Fin k ↪ Fin (j+k)` — the low (`Fin.castAdd`) and high (`Fin.natAdd`) coordinate blocks of a `(j+k)`-qubit register; `@[simp]` lemmas `lowEmb_apply`/`highEmb_apply`. The split coordinates `embed_kron_factor` factors a tensor across

**Key theorems:**
- `embed_one` — `embed qs 1 = 1`
- `embed_mul` — `embed qs (A * B) = embed qs A * embed qs B`
- `embed_conjTranspose` — `(embed qs U)ᴴ = embed qs Uᴴ`
- `embed_unitary` — `IsUnitary U → IsUnitary (embed qs U)`
- `embed_comm_disjoint` — gates on disjoint qubit sets commute (hypothesis `∀ a b, qs₁ a ≠ qs₂ b`)
- `embed_embed` — composition collapses the addressing maps: `embed qs (embed qs2 U) = embed (qs2.trans qs) U` (via the `selectIdx_trans` helper)
- `embed_kron_factor` — a tensor embedded at `qs` factors into its halves: `embed qs (kron A B) = embed (lowEmb.trans qs) A * embed (highEmb.trans qs) B`; the matrix fact behind `QCircuit.embed_par_split`. Helpers `selectIdx_lowEmb`/`selectIdx_highEmb` (and the per-bit `tensor_symm_fst_bit`/`tensor_symm_snd_bit`) align `selectIdx` with the `tensorIndexEquiv` low/high split
- `embed_refl` — the identity embedding is the gate: `embed (Function.Embedding.refl _) U = U` (via `selectIdx_refl`)
- `kron_eq_embed` — `kron A B = embed (lowEmb j k) A * embed (highEmb j k) B`; the matrix fact behind `QCircuit.par_as_embed` (`embed_kron_factor` at the identity embedding)
- `index_ext_iff` — `i = j ↔ AgreeOff qs i j ∧ selectIdx qs i = selectIdx qs j`
- `selectIdx_symm_apply`, `selectIdx_eq_of_bits` — bit-level characterizations of `selectIdx`
- `selectIdx_mergeBits` (`@[simp]`), `agreeOff_mergeBits`, `mergeBits_selectIdx`, `mergeBits_bit_mem`, `mergeBits_bit_not_mem` — `mergeBits`/`selectIdx` round-trips and per-bit values

---

## `Basic/EmbedState.lean`

Bridge from the `embed` matrix algebra to the *state* layer: how an embedded gate acts on a
computational basis ket. These are the lemmas circuit-correctness proofs use, since algorithm
inputs and intermediate states are (superpositions of) basis kets. Imports `Basic/Embed.lean`,
`Basic/Hilbert.lean`, and Mathlib's `Matrix.IsDiag`.

**Key theorems:**
- `isDiag_mul_ket` — generic: any diagonal matrix acts on a basis ket by its eigenvalue, `M * ket i = M i i • ket i`. The reusable fact behind every diagonal gate's action (Rz, S, T, CZ, controlled-Rₖ), not just embedded ones
- `embed_isDiag` — `Matrix.IsDiag U → Matrix.IsDiag (embed qs U)` (diagonal gates stay diagonal when embedded)
- `embed_diag_mul_ket` — **the workhorse**: a diagonal gate, embedded, acts on `ket i` by the scalar `U (selectIdx qs i) (selectIdx qs i)`, with no superposition: `embed qs U * ket i = U (selectIdx qs i) (selectIdx qs i) • ket i`. One line from `isDiag_mul_ket` + `embed_isDiag`; collapses an entire layer of controlled-phase/rotation gates, however addressed, into a phase read off the index bits
- `embed_mul_ket` — general action on a basis ket: `embed qs U * ket i = ∑ s, U s (selectIdx qs i) • ket (mergeBits qs i s)`
- `embed_single_mul_ket` — single-qubit (`k = 1`) specialization, splitting `ket i` into the two indices that clear/set the addressed qubit; the entry point for an embedded `H`
- `mul_ket_one` — a 1-qubit gate on a basis ket is its column: `U * ket t = U 0 t • ket 0 + U 1 t • ket 1`
- `selectIdx_singleEmb_last`, `mergeBits_singleEmb_last` — bridge `embed`'s `finFunctionFinEquiv` bit-addressing of the **top** qubit `Fin.last m` to `tensorIndexEquiv`'s tensor split: selecting the top qubit reads the high factor, and reconstructing it pairs `s` with `j`'s low bits
- `embedTop_mul_ket` — a 1-qubit gate embedded on the top qubit acts as `embed (singleEmb (Fin.last m)) U * ket j = tensorState (ket j_low) (U * ket j_top)`; the clean entry point for circuits that process the most significant qubit

---

## `Basic/Hilbert.lean`

State-level layer: quantum states, basis kets, tensor product of states.

**Key definitions:**
- `QVector n` — `Matrix (Fin (2^n)) (Fin 1) ℂ`; column-vector representation of a quantum state (a gate acts by plain matrix multiplication `U * ψ`)
- `IsNormalized ψ` — `∑ i, ‖ψ i 0‖^2 = 1`
- `ket i : QVector n` — basis state at index `i`; `ket i j _ = if j = i then 1 else 0` (no notation at this layer; the symbolic `❘i⟩` belongs to `QState.basis`)
- `allOnes n : Fin (2^n)` — the all-ones index `2^n - 1` (top index of `Fin (2^n)`); `ket (allOnes n)` is `|1…1⟩`. `@[simp]` lemma `allOnes_val : (allOnes n).val = 2^n - 1`
- `tensorState ψ φ : QVector (j+k)` — tensor product of two states

**Key theorems:**
- `ket_normalized` — every basis ket is normalized
- `mul_ket_apply` — `(M * ket i) r 0 = M r i` (multiplying by a basis ket reads off a single column)
- `ket_tensorState` — `tensorState (ket a) (ket b) = ket (tensorIndexEquiv j k ⟨a, b⟩)`
- `tensorState_smul_left`/`tensorState_smul_right`/`tensorState_add_left`/`tensorState_add_right` — bilinearity of `tensorState`
- `tensorState_assoc_one` — `tensorState (tensorState ψ φ) χ = tensorState ψ (tensorState φ χ)` for a 1-qubit third factor (types agree because `(j+k)+1 = j+(k+1)` definitionally); the fact behind `QState.tensor_assoc`
- `kron_tensorState` — `kron A B * tensorState ψ φ = tensorState (A * ψ) (B * φ)`
- `IsNormalized.tensorState` — tensor product preserves normalization

---

## `Gate/Standard.lean`

Standard gate matrices, unitarity proofs, and `QCircuit` abbreviations.

**Single-qubit gates** (`QMatrix 1`): `H`, `X`, `Y`, `Z`, `S`, `T`, `Rz θ`, `Rx θ`, `Ry θ`, `Rk k`

`Rk k = diag(1, e^{2πi/2ᵏ})` is the QFT phase gate (N&C §5.1); `R₁ = Z`, `R₂ = S`, `R₃ = T`. `Rk_isDiag` proves it diagonal; `controlled_isDiag` lifts diagonality through `controlled` (so `controlled (Rk k)` is diagonal — the fact the QFT rotation layers rely on).

**Phase-form matrix entries** (the only matrix-level facts the QFT correctness proof bottoms out at — wrapped by the embedded actions in `Gate/StateActions.lean`, so callers never touch raw entries): `H_row0 (t) : H 0 t = (√2)⁻¹` and `H_row1 (t) : H 1 t = (√2)⁻¹ · e^{2πi·t/2}` give the Hadamard's two rows in phase form; `controlled_Rk_diag (k) (idx) : (controlled (Rk k)) idx idx = if idx = 3 then e^{2πi/2ᵏ} else 1` gives the controlled-rotation eigenphase.

**Two-qubit gates** (`QMatrix 2`): `CNOT`, `CZ`, `SWAP`, `controlled U`

**Three-qubit gate** (`QMatrix 3`): `Toffoli`

All gate matrices follow the LSB-first qubit convention (see [conventions.md](conventions.md)).

**Unitarity theorems:** `isUnitary_H`, `isUnitary_X`, `isUnitary_Y`, `isUnitary_Z`, `isUnitary_S`, `isUnitary_T`, `isUnitary_CNOT`, `isUnitary_CZ`, `isUnitary_SWAP`, `isUnitary_Toffoli`, `isUnitary_controlled`, `isUnitary_Rz`, `isUnitary_Rx`, `isUnitary_Ry`, `isUnitary_Rk`

**State-action lemmas:** `Rz_ket_zero`, `Rz_ket_one`, `Rz_ket_diag`, `CNOT_ket_pair`; single-qubit actions `X_ket_zero`, `X_ket_one`, `Y_ket_zero`, `Y_ket_one`, `Z_ket_zero`, `Z_ket_one`, `S_ket_zero`, `S_ket_one`, `H_ket_zero`, `H_ket_one`

**QCircuit abbreviations** — `abbrev` wrappers that lift gate matrices into `QCircuit`:

| Abbrev | Type |
|---|---|
| `HGate`, `XGate`, `YGate`, `ZGate`, `SGate`, `TGate` | `QCircuit 1` |
| `RzGate θ`, `RxGate θ`, `RyGate θ`, `RkGate k` | `QCircuit 1` |
| `CNOTGate`, `CZGate`, `SWAPGate` | `QCircuit 2` |
| `ToffoliGate` | `QCircuit 3` |
| `ControlledGate U` | `QCircuit 2` |

**WF lemmas** (`@[simp]`, one per abbreviation): `wf_HGate` … `wf_ToffoliGate` discharge `QCircuit.WF` for each gate abbreviation; `wf_ControlledGate` takes the unitarity hypothesis `IsUnitary U`.

---

## `Gate/StateActions.lean`

Symbolic gate actions: `QState.Equiv` theorems for standard gates acting on the single-qubit basis kets `❘0⟩`/`❘1⟩` and tensor products (the `_bit0`/`_bit1` theorem-name suffixes refer to the acted-on bit value). These are the building blocks for correctness proofs that use `QCircuit.Equiv.basis_iff_state` to reduce a circuit equivalence to per-basis-state obligations.

Imports `Gate/Standard.lean`, `State/Rewrite.lean`, and `Circuit/Embed.lean` (for the embedded actions below); no circular dependency.

**Single-qubit actions** (all proved by unfolding `QState.Equiv` and applying the QVector lemmas from `Gate/Standard.lean`):

| Theorem | Statement |
|---|---|
| `XGate_bit0` | `XGate * ❘0⟩ ≈ ❘1⟩` |
| `XGate_bit1` | `XGate * ❘1⟩ ≈ ❘0⟩` |
| `YGate_bit0` | `YGate * ❘0⟩ ≈ I • ❘1⟩` |
| `YGate_bit1` | `YGate * ❘1⟩ ≈ (-I) • ❘0⟩` |
| `ZGate_bit0` | `ZGate * ❘0⟩ ≈ ❘0⟩` |
| `ZGate_bit1` | `ZGate * ❘1⟩ ≈ (-1) • ❘1⟩` |
| `SGate_bit0` | `SGate * ❘0⟩ ≈ ❘0⟩` |
| `SGate_bit1` | `SGate * ❘1⟩ ≈ I • ❘1⟩` |
| `HGate_bit0` | `HGate * ❘0⟩ ≈ (√2)⁻¹ • (❘0⟩ + ❘1⟩)` |
| `HGate_bit1` | `HGate * ❘1⟩ ≈ (√2)⁻¹ • (❘0⟩ + (-1) • ❘1⟩)` |

Parameterized over the basis index rather than fixed kets:
- `RzGate_basis (θ : ℝ) (a : Fin (2^1))` — `RzGate θ * ❘a⟩ ≈ exp((2a-1)·iθ/2) • ❘a⟩` (phase `exp(-iθ/2)` on `❘0⟩`, `exp(iθ/2)` on `❘1⟩`)

**Two-qubit actions:**
- `CNOTGate_basis_tensor (a b : Fin 2)` — `CNOTGate * (basis a ⊗ basis b) ≈ basis a ⊗ basis (a + b)`

**Embedded gate actions in phase form** — these lift the gate-agnostic `QCircuit.embed_single_action` / `embed_diag_action` (from `Circuit/Embed.lean`) to the two specific gates a positional algorithm like the QFT addresses, resolving the gate matrix entries to explicit phases *once*. Downstream proofs (e.g. `Examples/QFT.lean`) then stay entirely in the `QState` layer and never see a matrix entry:
- `embed_H_action (qs : Fin 1 ↪ Fin n) (x)` — `embed qs HGate * ❘x⟩ ≈ (√2)⁻¹ • ❘mergeBits qs x 0⟩ + ((√2)⁻¹ · e^{2πi·b/2}) • ❘mergeBits qs x 1⟩` where `b = selectIdx qs x` (the addressed bit); the `❘1⟩` branch carries the sign `(-1)ᵇ`
- `embed_controlled_Rk_action (qs : Fin 2 ↪ Fin n) (k) (x)` — `embed qs (ControlledGate (Rk k)) * ❘x⟩ ≈ (if selectIdx qs x = 3 then e^{2πi/2ᵏ} else 1) • ❘x⟩`; the embedded controlled rotation is diagonal, scaling by the phase exactly when both addressed qubits are set

---

## `Circuit/Type.lean`

The `QCircuit` inductive type and the type-cast combinator.

**Key definitions:**
- `QCircuit n` — inductive type with constructors `id`, `gate`, `seq`, `par`, `embed`
  - `embed (qs : Fin k ↪ Fin n) (c : QCircuit k) : QCircuit n` — places the `k`-qubit sub-circuit `c` at the qubits selected by `qs` (arbitrary injection); the addressing primitive `par` cannot express
  - Notation: `1` for `id`, `c₁ * c₂` for `seq`, `c₁ ⊗ c₂` for `par` (`infixl:100`, binding tighter than `*` at 70, matching Mathlib's `⊗ₖ` and the state-layer `⊗`); `embed` has no infix
- `QCircuit.castN (h : m = n) (c : QCircuit m) : QCircuit n` — transport a circuit along a propositional equality of qubit counts

`castN` is used to state `QCircuit.par_assoc`: `par (par c₁ c₂) c₃` and `par c₁ (par c₂ c₃)` live in different types, so associativity is an eval-level statement involving `castN`.

---

## `Circuit/Semantics.lean`

Denotational semantics and well-formedness.

**Key definitions:**
- `eval : QCircuit n → QMatrix n` — denotational semantics; the `embed` case is `eval (.embed qs c) = embed qs (eval c)` (the matrix `embed`). `@[simp]` lemmas `eval_id`, `eval_gate`, `eval_seq`, `eval_par`, `eval_embed`, `eval_castN`
- `QCircuit.WF : QCircuit n → Prop` — `def` by structural recursion asserting all `gate` leaves are unitary (the `embed` case is `WF (.embed qs c) = WF c`)
  - `@[simp]` iff lemmas: `wf_id`, `wf_gate`, `wf_seq`, `wf_par`, `wf_embed`

**Key theorems:**
- `QCircuit.eval_unitary` — `WF c → IsUnitary (eval c)`
- `wf_foldr_seq` — a `foldr` of sequenced well-formed factors over a list is well-formed: the `WF` induction for gate layers built as `l.foldr (fun a acc => f a * acc) init` (used by the QFT stage/swap layers)

---

## `State/Type.lean`

The `QState` inductive type and supporting infrastructure.

**Key definitions:**
- `QState n` — inductive syntax tree for `n`-qubit states; constructors:
  - `.basis i : QState n` — computational basis state for `i : Fin (2^n)`; notation `❘i⟩` (U+2758 light vertical bar; opt-in via `open scoped QLean.Notation`)
  - `.smul α s` — scalar multiple; `α • s` notation via `SMul ℂ` instance
  - `.add s t`  — superposition; `s + t` notation via `Add` instance
  - `.tensor s t` — tensor product; `s ⊗ t` notation (qubit count sums; `infixl:100`, aligned with the circuit-layer `⊗`)
  - `.apply C s` — circuit `C` acting on state expression `s`; `C * s` notation via `HMul (QCircuit n) (QState n) (QState n)` instance

---

## `State/Semantics.lean`

Denotational semantics and normalization for state expressions.

**Key definitions:**
- `QState.eval : QState n → QVector n` — denotational semantics; `@[simp]` lemmas `eval_basis`, `eval_smul`, `eval_add`, `eval_tensor`, `eval_apply`
- `QState.IsNormalized s` — `QLean.IsNormalized (eval s)`; predicate lifted from `QVector`

**Key theorems:**
- `QState.IsNormalized.tensor` — tensor product of normalized expressions is normalized

---

## `State/Rewrite.lean`

State expression equivalence and equational rewrite rules. Holds the `QState.*` rewrite lemmas; the `QCircuit.*` lemmas that act on state expressions live in `Circuit/Rewrite.lean`, which imports this module.

**Key definitions:**
- `QState.Equiv (s t : QState n) : Prop` — `eval s = eval t`; notation `s ≈ t`

`QState.Equiv` is an equivalence relation with `@[refl]`/`@[symm]`/`@[trans]` instances and a `Trans` instance for `calc` blocks.

**Congruence lemmas** (all `@[gcongr]`, so the `gcongr` tactic descends `≈` goals through these constructors to their leaves; see `docs/lean-api.md`):
- `QState.Equiv.apply_congr` — `≈` is a congruence for `apply`: if `s ≈ t` then `C * s ≈ C * t`
- `QState.Equiv.add_congr` — `≈` is a congruence for `add`
- `QState.Equiv.smul_congr` — `≈` is a congruence for `smul`
- `QState.Equiv.tensor_congr` — `≈` is a congruence for `tensor`

**Scalar algebra** (`QState.smul` is a bare `SMul`, so the `MulAction`/`Module` lemmas do not fire — these recover the scalar algebra symbolically):
- `QState.one_smul` — `(1 : ℂ) • s ≈ s`
- `QState.smul_smul` — `a • (b • s) ≈ (a * b) • s`
- `QState.smul_add` — `a • (s + t) ≈ a • s + a • t`

**Distributivity rules:**
- `QState.add_tensor_left` — `(s + t) ⊗ u ≈ s ⊗ u + t ⊗ u`
- `QState.tensor_add_right` — `s ⊗ (t + u) ≈ s ⊗ t + s ⊗ u`
- `QState.smul_tensor_left` — `(α • s) ⊗ t ≈ α • (s ⊗ t)`
- `QState.tensor_smul_right` — `s ⊗ (α • t) ≈ α • (s ⊗ t)`

**Tensor algebra and basis splits:**
- `QState.tensor_assoc` — `(s ⊗ t) ⊗ u ≈ s ⊗ (t ⊗ u)` (right-unit case, `u : QState 1`)
- `QState.ket_zero_tensor` — `(❘0⟩ : QState (j+k)) ≈ (❘0⟩ : QState j) ⊗ (❘0⟩ : QState k)`
- `QState.basis_tensor_split` — `❘tensorIndexEquiv j k ⟨a, b⟩⟩ ≈ ❘a⟩ ⊗ ❘b⟩`; the basis split underlying `QCircuit.Equiv.basis_iff_tensor` (generalizes `QState.ket_zero_tensor`)
- `QState.allOnes_succ` — `(❘allOnes (n+1)⟩ : QState (n+1)) ≈ ❘allOnes n⟩ ⊗ ❘1⟩`; the all-ones companion of `ket_zero_tensor` (splits off the top qubit), used in the GHZ example

---

## `Circuit/Rewrite.lean`

QCircuit equivalence and equational rewrite rules.

**Key definitions:**
- `QCircuit.Equiv (c₁ c₂ : QCircuit n) : Prop` — `eval c₁ = eval c₂`; notation `c₁ ≈ c₂`

`QCircuit.Equiv` is an equivalence relation with `@[refl]`/`@[symm]`/`@[trans]` instances and a `Trans` instance for `calc` blocks.

**Congruence lemmas** (both `@[gcongr]`, so `gcongr` descends `QCircuit.Equiv` goals through `seq`/`par`):
- `QCircuit.Equiv.seq_congr` — `≈` is a congruence for `seq`
- `QCircuit.Equiv.par_congr` — `≈` is a congruence for `par`

**Structural rewrite rules:**
- `QCircuit.seq_id_left` — `1 * c ≈ c`
- `QCircuit.seq_id_right` — `c * 1 ≈ c`
- `QCircuit.seq_assoc` — `(c₁ * c₂) * c₃ ≈ c₁ * (c₂ * c₃)`
- `QCircuit.par_assoc` — associativity of `⊗` up to `castN` (eval-level equality)
- `QCircuit.interchange_law` — `(a * b) ⊗ (c * d) ≈ (a ⊗ c) * (b ⊗ d)`

**Basis characterization:**
- `QCircuit.Equiv.basis_iff` — `c₁ ≈ c₂ ↔ ∀ i, eval c₁ * ket i = eval c₂ * ket i`; useful for basis-state proofs

**QCircuit action on symbolic states** (the `QCircuit.*` lemmas that reshape an `apply` expression `C * s`; used as `calc`/`grw` steps, building on `QState.Equiv` from `State/Rewrite.lean`):
- `QCircuit.apply_add` — `C * (s + t) ≈ C * s + C * t`
- `QCircuit.apply_smul` — `C * (α • s) ≈ α • (C * s)`
- `QCircuit.seq_action` — `(c₁ * c₂) * s ≈ c₁ * (c₂ * s)` (`c₂`, the rightmost factor, acts first)
- `QCircuit.id_action` — `(1 : QCircuit n) * s ≈ s`
- `QCircuit.par_action_tensor` — `(c₁ ⊗ c₂) * (s ⊗ t) ≈ (c₁ * s) ⊗ (c₂ * t)`

**Symbolic-state equivalence criteria** (characterize `QCircuit.Equiv` through the symbolic `QState` layer; together with the action lemmas above, this is why `Circuit/Rewrite.lean` imports `State/Rewrite.lean`):
- `QCircuit.Equiv.apply_state` — equivalent circuits act identically on a state: if `c₁ ≈ c₂` then `c₁ * s ≈ c₂ * s`
- `QCircuit.Equiv.basis_iff_state` — `c₁ ≈ c₂ ↔ ∀ i, c₁ * ❘i⟩ ≈ c₂ * ❘i⟩` (symbolic-basis form of `basis_iff`)
- `QCircuit.Equiv.equiv_iff_all_states` — `c₁ ≈ c₂ ↔ ∀ s, c₁ * s ≈ c₂ * s`
- `QCircuit.Equiv.basis_iff_tensor` — for `c₁ c₂ : QCircuit (j+k)`, `c₁ ≈ c₂ ↔ ∀ (a : Fin (2^j)) (b : Fin (2^k)), c₁ * (❘a⟩ ⊗ ❘b⟩) ≈ c₂ * (❘a⟩ ⊗ ❘b⟩)`; factored-basis criterion that pairs with the tensor-form gate actions in `Gate/StateActions.lean`

---

## `Circuit/Embed.lean`

Circuit-level algebra of the `embed` constructor — `≈`-lemmas lifting the matrix algebra of
`Basic/Embed.lean` to `QCircuit`, plus basis-ket action lemmas. Imports `Circuit/Rewrite.lean` and
`Basic/EmbedState.lean`. See [architecture.md](architecture.md) *Embedding as a circuit constructor*.

**Circuit-algebra lemmas** (all `QCircuit.Equiv`, each reducing to the matrix algebra):
- `QCircuit.embed_gate` — bridge: `embed qs (gate U) ≈ gate (embedₘ qs U)` (`rfl`)
- `QCircuit.embed_id` — `embed qs 1 ≈ 1`
- `QCircuit.embed_seq` — distributes over sequencing: `embed qs (c₁ * c₂) ≈ embed qs c₁ * embed qs c₂`
- `QCircuit.embed_comp` — nested embeddings compose: `embed qs (embed qs2 c) ≈ embed (qs2.trans qs) c`
- `QCircuit.embed_par_split` — `embed qs (c₁ ⊗ c₂) ≈ embed (lowEmb.trans qs) c₁ * embed (highEmb.trans qs) c₂` (the embedded form)
- `QCircuit.par_as_embed` — `c₁ ⊗ c₂ ≈ embed (lowEmb) c₁ * embed (highEmb) c₂`; normalizes a bare `par` into the `embed` view for a structural pass
- `QCircuit.embed_comm_disjoint` — embedded sub-circuits on disjoint qubit sets commute

**Action lemmas** (`QState.Equiv`; the entry points for per-layer correctness proofs):
- `QCircuit.embed_diag_action` — a diagonal gate embedded at `qs` scales a basis ket: `embed qs (gate U) * ❘i⟩ ≈ U (selectIdx qs i) (selectIdx qs i) • ❘i⟩` (lifts `embed_diag_mul_ket`)
- `QCircuit.embed_single_action` — a 1-qubit gate embedded at `qs 0` splits `❘i⟩` into the two indices that clear/set that qubit (lifts `embed_single_mul_ket`)

---

## `Program/Angle.lean`

Symbolic, serializable rotation angles. `Angle := ℚ`, interpreted as a multiple of `π`.

- `Angle.denote (a : Angle) : ℝ` — the real angle `a · π` (noncomputable; uses `Real.pi`)
- `Angle.toQASM (a : Angle) : String` — OpenQASM rendering of `a · π` (`0 ↦ "0"`, `1 ↦ "pi"`, `1/4 ↦ "pi/4"`, `3/4 ↦ "3*pi/4"`, `-1/2 ↦ "-pi/2"`, `2 ↦ "2*pi"`)

`denote`/`toQASM` are the only interface, so a richer symbolic-expression `Angle` can replace this without touching callers.

## `Program/Basis.lean`

The named basis-gate enum `Prim` — a serializable alternative to `QCircuit.gate`'s opaque matrix. Imports `Gate/Standard.lean`.

- `Prim` — `H/X/Y/Z/S/T`, `Rz/Rx/Ry (a : Angle)`, `Rk (k : ℕ)`, `CX/CZ/SWAP`, `CRk (k : ℕ)` (`deriving DecidableEq, Repr`)
- `Prim.arity : Prim → ℕ` — qubit count (computable)
- `Prim.matrix : (g : Prim) → QMatrix g.arity` — denotation to the concrete `Gate/Standard` gate (noncomputable; gate RHS are `_root_`-qualified, see [lean-api.md](lean-api.md))
- `Prim.isUnitary (g : Prim) : IsUnitary g.matrix` — one `isUnitary_*` lemma per constructor
- `Prim.rkAngle (k : ℕ) : Angle` — `Rk k`'s QASM phase, `2/2^k` (so `R₁=p(pi)`, `R₂=p(pi/2)`, `R₃=p(pi/4)`)
- `Prim.toQASM : Prim → String` — mnemonic with symbolic parameter (`Rk`/`CRk` emit `p(…)`/`cp(…)`)

Extending the basis = one constructor + one line in each of `arity`/`matrix`/`isUnitary`/`toQASM`.

## `Program/Type.lean`

The `Program` IR and its denotation. Imports `Program/Basis.lean`, `Circuit/Semantics.lean`.

- `Program : ℕ → Type` — `id`, `prim (g : Prim) (Fin g.arity ↪ Fin n)`, `seq`; `1 = id`, `* = seq` (no `par` — flat, QASM-aligned). Stores no matrices, only names/angles/indices (computable, serializable).
- `Program.denote : Program n → QCircuit n` — `prim g qs ↦ embed qs (gate g.matrix)`, `seq ↦ *`, `id ↦ 1` (noncomputable; the only bridge to the semantic layer)
- `Program.denote_id`/`denote_prim`/`denote_seq` — `@[simp]` homomorphism lemmas
- `Program.denote_WF (p) : p.denote.WF` and `Program.denote_unitary (p) : IsUnitary (eval p.denote)` — **unconditional** (always-unitary primitives + injective operands ⇒ no side condition)
- `Program.ofList (g : Prim) (qs : List (Fin n)) : Option (Program n)` — smart constructor; succeeds iff `qs.length = g.arity ∧ qs.Nodup` (both decidable), building the `↪` from the deduped list
- `Program.relabel (f : Fin n ↪ Fin m) : Program n → Program m` — re-address every gate through `f` (move a sub-block onto a chosen qubit window: `prim g qs ↦ prim g (qs.trans f)`)

## `Program/QASM.lean`

OpenQASM 3.0 emission. Imports `Program/Type.lean`. Fully **computable** — reads only gate names, symbolic angles, and qubit indices; never a matrix, never `denote`.

- `qasmQubit (i : Fin n) : String` — `q[i]`
- `Program.instrLine (g) (qs) : String` — one gate-application line (gate-qubit `i` → physical `qs i`)
- `Program.bodyLines : Program n → List String` — lines in execution order (`seq p q` runs `q` first, so `q`'s lines precede `p`'s)
- `Program.toQASM (p : Program n) : String` — full program string (`OPENQASM 3.0;` header, `qubit[n] q;` register, body)

The emitter is **trusted** (we do not formalize OpenQASM's semantics); what is verified is everything upstream (`denote_unitary`, and per-program `denote ≈ target` theorems).

## `Program/Rewrite.lean`

Equational lemmas about `Program.denote`, used to relate a program to a target circuit. Imports `Program/Type.lean`, `Circuit/Embed.lean`.

- `QCircuit.embed_congr (qs) (h : c₁ ≈ c₂) : embed qs c₁ ≈ embed qs c₂` — embedding respects `≈` (`@[gcongr]`, so `grw` can rewrite under an `embed`)
- `Program.denote_foldr_seq (l) (P) (init)` — `denote` commutes with a right-fold of sequenced gates: `(l.foldr (P · * ·) init).denote = l.foldr ((P ·).denote * ·) init.denote` (an equality; each step is `denote_seq`)
- `Program.denote_relabel (f) (p) : (p.relabel f).denote ≈ embed f p.denote` — re-addressing denotes to the embedding of the denotation (via `embed_id`/`embed_comp`/`embed_seq`)
