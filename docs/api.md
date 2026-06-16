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
- `kron_assoc` — associativity of `kron` up to `reindex` (used in `par_assoc`)
- `IsUnitary.kron` — `IsUnitary A → IsUnitary B → IsUnitary (kron A B)`
- `kron_mul_ket` — `kron A B * ket (tensorIndexEquiv j k ⟨a, b⟩) = tensorState (A * ket a) (B * ket b)`
- `tensorIndexEquiv_symm_fst_val`, `tensorIndexEquiv_symm_snd_val` — decompose an index into its low and high parts

---

## `Basic/Hilbert.lean`

State-level layer: quantum states, basis kets, tensor product of states.

**Key definitions:**
- `QVector n` — `Matrix (Fin (2^n)) (Fin 1) ℂ`; column-vector representation of a quantum state
- `IsNormalized ψ` — `∑ i, ‖ψ i 0‖^2 = 1`
- `ket i : QVector n` — basis state at index `i`; `ket i j _ = if j = i then 1 else 0`
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

Standard gate matrices, unitarity proofs, and `Circuit` abbreviations.

**Single-qubit gates** (`QMatrix 1`): `H`, `X`, `Y`, `Z`, `S`, `T`, `Rz θ`, `Rx θ`, `Ry θ`

**Two-qubit gates** (`QMatrix 2`): `CNOT`, `CZ`, `SWAP`, `controlled U`

**Three-qubit gate** (`QMatrix 3`): `Toffoli`

All gate matrices follow the LSB-first qubit convention (see [conventions.md](conventions.md)).

**Unitarity theorems:** `isUnitary_H`, `isUnitary_X`, `isUnitary_Y`, `isUnitary_Z`, `isUnitary_S`, `isUnitary_T`, `isUnitary_CNOT`, `isUnitary_CZ`, `isUnitary_SWAP`, `isUnitary_controlled`, `isUnitary_Rz`, `isUnitary_Rx`, `isUnitary_Ry`

**State-action lemmas:** `Rz_ket_zero`, `Rz_ket_one`, `Rz_ket_diag`, `CNOT_ket_pair`, `CNOT_tensorState_smul_ket`

**Circuit abbreviations** — `abbrev` wrappers that lift gate matrices into `Circuit`:

| Abbrev | Type |
|---|---|
| `HGate`, `XGate`, `YGate`, `ZGate`, `SGate`, `TGate` | `Circuit 1` |
| `RzGate θ`, `RxGate θ`, `RyGate θ` | `Circuit 1` |
| `CNOTGate`, `CZGate`, `SWAPGate` | `Circuit 2` |
| `ToffoliGate` | `Circuit 3` |
| `ControlledGate U` | `Circuit 2` |

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

## `Circuit/Type.lean`

The `Circuit` inductive type and the type-cast combinator.

**Key definitions:**
- `Circuit n` — inductive type with constructors `id`, `gate`, `seq`, `par`
  - Notation: `1` for `id`, `c₁ * c₂` for `seq`, `c₁ + c₂` for `par`
- `Circuit.castN (h : m = n) (c : Circuit m) : Circuit n` — transport a circuit along a propositional equality of qubit counts

`castN` is used to state `par_assoc`: `par (par c₁ c₂) c₃` and `par c₁ (par c₂ c₃)` live in different types, so associativity is an eval-level statement involving `castN`.

---

## `Circuit/Semantics.lean`

Denotational semantics, well-formedness, and state-level circuit predicates.

**Key definitions:**
- `eval : Circuit n → QMatrix n` — denotational semantics; `@[simp]` lemmas `eval_id`, `eval_gate`, `eval_seq`, `eval_par`, `eval_castN`
- `Circuit.WF : Circuit n → Prop` — inductive predicate asserting all `gate` leaves are unitary
  - `@[simp]` iff lemmas: `wf_id`, `wf_gate`, `wf_seq`, `wf_par`
- `Circuit.maps (C : Circuit n) (φ ψ : QVector n) : Prop` — `eval C * ket 0 = ψ` after applying to φ; `eval C * φ = ψ`
- `Circuit.prepares (C : Circuit n) (ψ : QVector n)` — `C.maps (ket 0) ψ`

**Key theorems:**
- `Circuit.eval_unitary` — `WF c → IsUnitary (eval c)`
- `Circuit.maps_id` — identity circuit maps any state to itself
- `Circuit.maps_comp` — sequential composition chains `maps`
- `Circuit.maps_iff` — `C.maps φ ψ ↔ eval C * φ = ψ`

---

## `State/Type.lean`

The `QState` inductive type and supporting infrastructure.

**Key definitions:**
- `QState n` — inductive syntax tree for `n`-qubit states; constructors:
  - `.basis i : QState n` — computational basis state `|i⟩` for `i : Fin (2^n)`
  - `.smul α s` — scalar multiple; `α • s` notation via `SMul ℂ` instance
  - `.add s t`  — superposition; `s + t` notation via `Add` instance
  - `.tensor s t` — tensor product; `s ⊗ₛ t` notation (qubit count sums)
- `QState.castN (h : m = n) : QState m → QState n` — transport along a qubit-count equality
- `QState.bit0 : QState 1`, `QState.bit1 : QState 1` — single-qubit `|0⟩` and `|1⟩` shorthands

---

## `State/Semantics.lean`

Denotational semantics and the circuit–state bridge.

**Key definitions:**
- `QState.eval : QState n → QVector n` — denotational semantics; `@[simp]` lemmas `eval_basis`, `eval_smul`, `eval_add`, `eval_tensor`, `eval_castN`
- `QState.IsNormalized s` — `QLean.IsNormalized (eval s)`; predicate lifted from `QVector`
- `Circuit.mapsExpr C s t` — `C.maps (eval s) (eval t)`; lifts `Circuit.maps` to state expressions

**Key theorems:**
- `QState.IsNormalized.tensor` — tensor product of normalized expressions is normalized
- `Circuit.maps_tensor` — if `c₁.mapsExpr s s'` and `c₂.mapsExpr t t'` then `(c₁ + c₂).mapsExpr (s ⊗ₛ t) (s' ⊗ₛ t')`

---

## `State/Rewrite.lean`

State expression equivalence and equational rewrite rules.

**Key definitions:**
- `QState.Equiv (s t : QState n) : Prop` — `eval s = eval t`; notation `s ≈ t`

`QState.Equiv` is an equivalence relation with `@[refl]`/`@[symm]`/`@[trans]` instances and a `Trans` instance for `calc` blocks.

**Congruence lemmas:**
- `QState.Equiv.add_congr` — `≈` is a congruence for `add`
- `QState.Equiv.smul_congr` — `≈` is a congruence for `smul`
- `QState.Equiv.tensor_congr` — `≈` is a congruence for `tensor`

**Distributivity rules:**
- `QState.add_tensor_left` — `(s + t) ⊗ₛ u ≈ s ⊗ₛ u + t ⊗ₛ u`
- `QState.tensor_add_right` — `s ⊗ₛ (t + u) ≈ s ⊗ₛ t + s ⊗ₛ u`
- `QState.smul_tensor_left` — `(α • s) ⊗ₛ t ≈ α • (s ⊗ₛ t)`
- `QState.tensor_smul_right` — `s ⊗ₛ (α • t) ≈ α • (s ⊗ₛ t)`

---

## `Circuit/Rewrite.lean`

Circuit equivalence and equational rewrite rules.

**Key definitions:**
- `Circuit.Equiv (c₁ c₂ : Circuit n) : Prop` — `eval c₁ = eval c₂`; notation `c₁ ≈ c₂`

`Circuit.Equiv` is an equivalence relation with `@[refl]`/`@[symm]`/`@[trans]` instances and a `Trans` instance for `calc` blocks.

**Congruence lemmas:**
- `Circuit.Equiv.seq_congr` — `≈` is a congruence for `seq`
- `Circuit.Equiv.par_congr` — `≈` is a congruence for `par`

**Structural rewrite rules:**
- `seq_id_left` — `1 * c ≈ c`
- `seq_id_right` — `c * 1 ≈ c`
- `seq_assoc` — `(c₁ * c₂) * c₃ ≈ c₁ * (c₂ * c₃)`
- `par_assoc` — associativity of `+` up to `castN` (eval-level equality)
- `interchange_law` — `(a * b) + (c * d) ≈ (a + c) * (b + d)`

**Basis characterization:**
- `Circuit.Equiv.basis_iff` — `c₁ ≈ c₂ ↔ ∀ i, eval c₁ * ket i = eval c₂ * ket i`; useful for basis-state proofs
