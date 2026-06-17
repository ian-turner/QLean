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
- `kron_mul_ket` — `kron A B * ket (tensorIndexEquiv j k ⟨a, b⟩) = tensorState (A * ket a) (B * ket b)`
- `tensorIndexEquiv_symm_fst_val`, `tensorIndexEquiv_symm_snd_val` — decompose an index into its low and high parts

---

## `Basic/Hilbert.lean`

State-level layer: quantum states, basis kets, tensor product of states.

**Key definitions:**
- `QVector n` — `Matrix (Fin (2^n)) (Fin 1) ℂ`; column-vector representation of a quantum state
- `IsNormalized ψ` — `∑ i, ‖ψ i 0‖^2 = 1`
- `ket i : QVector n` — basis state at index `i`; `ket i j _ = if j = i then 1 else 0`; notation `|i⟩`
- `tensorState ψ φ : QVector (j+k)` — tensor product of two states
- `act U ψ` — matrix-vector action `U * ψ`

**Key theorems:**
- `ket_normalized` — every basis ket is normalized
- `ket_inner` — `(ket i)ᴴ * ket j = if i = j then 1 else 0`
- `ket_tensorState` — `tensorState (ket a) (ket b) = ket (tensorIndexEquiv j k ⟨a, b⟩)`
- `kron_tensorState` — `kron A B * tensorState ψ φ = tensorState (A * ψ) (B * φ)`
- `IsNormalized.tensorState` — tensor product preserves normalization
- `act_mul`, `act_one`

---

## `Gate/Standard.lean`

Standard gate matrices, unitarity proofs, and `QCircuit` abbreviations.

**Single-qubit gates** (`QMatrix 1`): `H`, `X`, `Y`, `Z`, `S`, `T`, `Rz θ`, `Rx θ`, `Ry θ`

**Two-qubit gates** (`QMatrix 2`): `CNOT`, `CZ`, `SWAP`, `controlled U`

**Three-qubit gate** (`QMatrix 3`): `Toffoli`

All gate matrices follow the LSB-first qubit convention (see [conventions.md](conventions.md)).

**Unitarity theorems:** `isUnitary_H`, `isUnitary_X`, `isUnitary_Y`, `isUnitary_Z`, `isUnitary_S`, `isUnitary_T`, `isUnitary_CNOT`, `isUnitary_CZ`, `isUnitary_SWAP`, `isUnitary_controlled`, `isUnitary_Rz`, `isUnitary_Rx`, `isUnitary_Ry`

**State-action lemmas:** `Rz_ket_zero`, `Rz_ket_one`, `Rz_ket_diag`, `CNOT_ket_pair`, `CNOT_tensorState_smul_ket`; single-qubit actions `X_ket_zero`, `X_ket_one`, `Y_ket_zero`, `Y_ket_one`, `Z_ket_zero`, `Z_ket_one`, `S_ket_zero`, `S_ket_one`, `H_ket_zero`, `H_ket_one`

**QCircuit abbreviations** — `abbrev` wrappers that lift gate matrices into `QCircuit`:

| Abbrev | Type |
|---|---|
| `HGate`, `XGate`, `YGate`, `ZGate`, `SGate`, `TGate` | `QCircuit 1` |
| `RzGate θ`, `RxGate θ`, `RyGate θ` | `QCircuit 1` |
| `CNOTGate`, `CZGate`, `SWAPGate` | `QCircuit 2` |
| `ToffoliGate` | `QCircuit 3` |
| `ControlledGate U` | `QCircuit 2` |

---

## `Gate/Embed.lean`

Embed a k-qubit gate into an n-qubit system at chosen qubit positions.

**Key definitions:**
- `gateAt (qs : Fin k ↪ Fin n) (U : QMatrix k) : QMatrix n` — U acts on the positions given by `qs`; identity on the complement. Defined by a direct matrix-entry formula (no permutation matrix).
- `hadamardAt (i : Fin n) : QMatrix n` — H at qubit `i`
- `cnotAt (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : QMatrix n` — CNOT with given control and target
- `controlledAt (ctrl tgt : Fin n) (h : ctrl ≠ tgt) (U : QMatrix 1) : QMatrix n` — controlled-U

**Key theorems:**
- `gateAt_mul` — `gateAt qs (A * B) = gateAt qs A * gateAt qs B`
- `gateAt_one` — `gateAt qs 1 = 1` (`@[simp]`)
- `gateAt_conjTranspose` — `(gateAt qs U)ᴴ = gateAt qs Uᴴ`
- `gateAt_unitary` — `IsUnitary U → IsUnitary (gateAt qs U)`
- `gateAt_comm_disjoint` — disjoint embeddings commute: `Disjoint (range qs₁) (range qs₂) → gateAt qs₁ A * gateAt qs₂ B = gateAt qs₂ B * gateAt qs₁ A`
- `isUnitary_hadamardAt`, `isUnitary_cnotAt`, `isUnitary_controlledAt`

---

## `Gate/StateActions.lean`

Symbolic gate actions: `QState.Equiv` theorems for standard gates acting on `QState.bit0`/`bit1` and tensor products. These are the building blocks for correctness proofs that use `QCircuit.Equiv.basis_iff_state` to reduce a circuit equivalence to per-basis-state obligations.

Imports `Gate/Standard.lean` and `State/Rewrite.lean`; no circular dependency.

**Single-qubit actions** (all proved by unfolding `QState.Equiv` and applying the QVector lemmas from `Gate/Standard.lean`):

| Theorem | Statement |
|---|---|
| `XGate_bit0` | `XGate * bit0 ≈ bit1` |
| `XGate_bit1` | `XGate * bit1 ≈ bit0` |
| `YGate_bit0` | `YGate * bit0 ≈ I • bit1` |
| `YGate_bit1` | `YGate * bit1 ≈ (-I) • bit0` |
| `ZGate_bit0` | `ZGate * bit0 ≈ bit0` |
| `ZGate_bit1` | `ZGate * bit1 ≈ (-1) • bit1` |
| `SGate_bit0` | `SGate * bit0 ≈ bit0` |
| `SGate_bit1` | `SGate * bit1 ≈ I • bit1` |
| `HGate_bit0` | `HGate * bit0 ≈ (√2)⁻¹ • (bit0 + bit1)` |
| `HGate_bit1` | `HGate * bit1 ≈ (√2)⁻¹ • (bit0 + (-1) • bit1)` |

Parameterized over the basis index rather than `bit0`/`bit1`:
- `RzGate_basis (θ : ℝ) (a : Fin (2^1))` — `RzGate θ * ❘a⟩ ≈ exp((2a-1)·iθ/2) • ❘a⟩` (phase `exp(-iθ/2)` on `❘0⟩`, `exp(iθ/2)` on `❘1⟩`)

**Two-qubit actions:**
- `CNOTGate_basis_tensor (a b : Fin 2)` — `CNOTGate * (basis a ⊗ basis b) ≈ basis a ⊗ basis (a + b)`

---

## `Circuit/Type.lean`

The `QCircuit` inductive type and the type-cast combinator.

**Key definitions:**
- `QCircuit n` — inductive type with constructors `id`, `gate`, `seq`, `par`
  - Notation: `1` for `id`, `c₁ * c₂` for `seq`, `c₁ + c₂` for `par`
- `QCircuit.castN (h : m = n) (c : QCircuit m) : QCircuit n` — transport a circuit along a propositional equality of qubit counts

`castN` is used to state `QCircuit.par_assoc`: `par (par c₁ c₂) c₃` and `par c₁ (par c₂ c₃)` live in different types, so associativity is an eval-level statement involving `castN`.

---

## `Circuit/Semantics.lean`

Denotational semantics and well-formedness.

**Key definitions:**
- `eval : QCircuit n → QMatrix n` — denotational semantics; `@[simp]` lemmas `eval_id`, `eval_gate`, `eval_seq`, `eval_par`, `eval_castN`
- `QCircuit.WF : QCircuit n → Prop` — inductive predicate asserting all `gate` leaves are unitary
  - `@[simp]` iff lemmas: `wf_id`, `wf_gate`, `wf_seq`, `wf_par`

**Key theorems:**
- `QCircuit.eval_unitary` — `WF c → IsUnitary (eval c)`

---

## `State/Type.lean`

The `QState` inductive type and supporting infrastructure.

**Key definitions:**
- `QState n` — inductive syntax tree for `n`-qubit states; constructors:
  - `.basis i : QState n` — computational basis state for `i : Fin (2^n)`; notation `|i⟩` (opt-in via `open scoped QLean.Notation`)
  - `.smul α s` — scalar multiple; `α • s` notation via `SMul ℂ` instance
  - `.add s t`  — superposition; `s + t` notation via `Add` instance
  - `.tensor s t` — tensor product; `s ⊗ t` notation (qubit count sums)
  - `.apply C s` — circuit `C` acting on state expression `s`; `C * s` notation via `HMul (QCircuit n) (QState n) (QState n)` instance
- `QState.castN (h : m = n) : QState m → QState n` — transport along a qubit-count equality
- `QState.bit0 : QState 1`, `QState.bit1 : QState 1` — single-qubit `|0⟩` and `|1⟩` shorthands

---

## `State/Semantics.lean`

Denotational semantics and normalization for state expressions.

**Key definitions:**
- `QState.eval : QState n → QVector n` — denotational semantics; `@[simp]` lemmas `eval_basis`, `eval_smul`, `eval_add`, `eval_tensor`, `eval_apply`; plus the non-`simp` `eval_castN`
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

**Distributivity rules:**
- `QState.add_tensor_left` — `(s + t) ⊗ u ≈ s ⊗ u + t ⊗ u`
- `QState.tensor_add_right` — `s ⊗ (t + u) ≈ s ⊗ t + s ⊗ u`
- `QState.smul_tensor_left` — `(α • s) ⊗ t ≈ α • (s ⊗ t)`
- `QState.tensor_smul_right` — `s ⊗ (α • t) ≈ α • (s ⊗ t)`

**Tensor algebra and basis splits:**
- `QState.tensor_assoc` — `(s ⊗ t) ⊗ u ≈ s ⊗ (t ⊗ u)` (right-unit case, `u : QState 1`)
- `QState.ket_zero_tensor` — `(❘0⟩ : QState (j+k)) ≈ (❘0⟩ : QState j) ⊗ (❘0⟩ : QState k)`
- `QState.basis_tensor_split` — `❘tensorIndexEquiv j k ⟨a, b⟩⟩ ≈ ❘a⟩ ⊗ ❘b⟩`; the basis split underlying `QCircuit.Equiv.basis_iff_tensor` (generalizes `QState.ket_zero_tensor`)

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
