# Changelog

One entry per commit. Newest first. Categories: `Added`, `Changed`, `Fixed`, `Removed`.

---

## [2026-06-17] (13)

### Removed
- `Gate/Embed.lean`: removed the entire positional gate-embedding module (`gateAt`, `hadamardAt`, `cnotAt`, `controlledAt`, and the `gateAt_*` algebra including `gateAt_comm_disjoint`) — an unused v1 leftover never wired into `QCircuit`/`eval`/`WF` or the `QState` layer; circuit positioning is handled structurally via `par`/`⊗`

---

## [2026-06-17] (12)

### Fixed
- `Gate/Standard.lean`: dropped the redundant trailing `<;> ring` from the six `*_ket_*` lemmas (`Y_ket_zero`, `Y_ket_one`, `Z_ket_one`, `S_ket_one`, `H_ket_zero`, `H_ket_one`); `simp` already closes every goal, so the `ring` raised `unreachableTactic`/`unusedTactic` linter warnings

---

## [2026-06-17] (11)

### Added
- `Examples/GHZState.lean`: symbolic preparation of the `(n+1)`-qubit GHZ state — `ghzCircuit n`/`ghzState n`, `wf_ghzCircuit`, and `ghzCircuit_prepares` (`ghzCircuit n * ❘0⟩ ≈ ghzState n`) proved by induction; the first example to need tensor re-association (`QState.tensor_assoc`) for GHZ's straddling CNOT cascade
- `QState.allOnes_succ` (`State/Rewrite.lean`): the all-ones ket splits off its top qubit, `❘allOnes (n+1)⟩ ≈ ❘allOnes n⟩ ⊗ ❘1⟩` — the all-ones companion of `ket_zero_tensor`
- `allOnes n : Fin (2^n)` with `@[simp]` `allOnes_val` (`Basic/Hilbert.lean`): the all-ones computational basis index `2^n - 1`
- `tensorIndexEquiv_apply_val` (`Basic/Tensor.lean`): forward value of the tensor index map, `(tensorIndexEquiv j k p).val = p.1 + p.2 * 2^j`

---

## [2026-06-16] (10)

### Changed
- Removed redundant `: QState n` ket annotations across `Gate/StateActions.lean`, `State/Rewrite.lean`, `Circuit/Rewrite.lean`, and `Examples/`: only a bare-numeral ket whose `n` is still unknown when the index elaborates (the gate-applied LHS ket, the LHS of `ket_zero_tensor`) needs one; RHS kets infer `n` through `≈`, `def`-body kets infer it from the return type, and variable-index kets (`❘a⟩`, `a : Fin (2^1)`) infer it from the index. Documented the rule in `docs/lean-api.md`

---

## [2026-06-16] (9)

### Changed
- Renamed the `Circuit` type to `QCircuit` (and its namespace; the `Circuit/` module/directory name is unchanged, mirroring `QState` in `State/`). All qualified names move accordingly: `QCircuit.WF`, `QCircuit.eval`, `QCircuit.Equiv`, `QCircuit.castN`, the rewrite lemmas, etc.

---

## [2026-06-16] (8)

### Changed
- Reorganized the rewrite layer by namespace: moved all `Circuit.*` lemmas (state-action lemmas `apply_add`/`apply_smul`/`seq_action`/`id_action`/`par_action_tensor` and criteria `Circuit.Equiv.apply_state`/`basis_iff_state`/`equiv_iff_all_states`/`basis_iff_tensor`) from `State/Rewrite.lean` to `Circuit/Rewrite.lean` (which now imports `State/Rewrite.lean`, not the reverse), and wrapped both files in their `QState`/`Circuit` namespaces — `QState.*` lemmas live in `State/Rewrite`, `Circuit.*` in `Circuit/Rewrite`; full names unchanged except the structural lemmas `seq_id_left`/`seq_id_right`/`seq_assoc`/`par_assoc`/`interchange_law`, which gained the `Circuit.` prefix

---

## [2026-06-16] (7)

### Changed
- `State/Type.lean`: renamed the state tensor notation `⊗ₛ` to `⊗`, overloading the circuit tensor symbol (disambiguated by operand type); updated all usage sites and docs
- `Circuit/Semantics.lean`: reversed sequential composition to matrix-multiplication order — `eval (c₁ * c₂) = eval c₁ * eval c₂`, so the rightmost factor acts first; `Circuit.seq_action` now reads `(c₁ * c₂) * s ≈ c₁ * (c₂ * s)`, and `Examples/BellState.lean`'s `bellCircuit` is reordered to `CNOTGate * (HGate ⊗ 1)`

### Fixed
- `docs/architecture.md`: corrected the `par` notation from `+` to `⊗`

---

## [2026-06-16] (6)

### Added
- `Examples/BellState.lean`: Bell-state preparation example — `bellCircuit` (H on qubit 0 then CNOT), `wf_bellCircuit`, the entangled `bellState` (`|Φ⁺⟩`), and `bellCircuit_prepares` proving `bellCircuit * ❘00⟩ ≈ bellState` by a single `grw` chain

---

## [2026-06-16] (5)

### Removed
- `Circuit/Semantics.lean`: dropped the unused state transformation/preparation predicates (`Circuit.maps`, `maps_iff`, `prepares`, `maps_id`, `maps_comp`) and the now-unneeded `Basic.Hilbert` import

### Fixed
- Docs: reconciled `docs/` and `CLAUDE.md` with the source — removed stale references to the deleted `Circuit.mapsExpr`/`maps_tensor`/`mapsExpr_iff` and to the dropped GHZ/QFT examples; documented the previously-undocumented circuit-action lemmas in `State/Rewrite.lean`

---

## [2026-06-16] (4)

### Removed
- `Examples/QFT.lean`: dropped the QFT example (`qftMatrix`, `isUnitary_qftMatrix`, `QFTGate_maps_ket`, `qftMatrix_one_eq_H`) and its `docs`/`references.md` entries; to be reinstated later

---

## [2026-06-16] (3)

### Added
- `Examples/HadamardTransform.lean`: symbolic `plusState`/`uniformSuperState` (`QState`), a tensor power of `|+⟩`

### Changed
- `Examples/HadamardTransform.lean`: `hadamardTransform_prepares` now states `hadamardTransform n * ❘0⟩ ≈ uniformSuperState n` and is proved by a single `grw` chain per induction step, like `rz_commutes_cnot`

### Removed
- `Examples/HadamardTransform.lean`: dropped the concrete `uniformSuper` amplitude vector and the `tensorIndexEquiv`/`kron_mul_ket` index-chasing proof, along with helpers `tensorIndexEquiv_zero_zero`, `tensorState_uniformSuper`, and the local raw `H_ket_zero`

---

## [2026-06-16] (2)

### Changed
- `Examples/RzCNOT.lean`: `rz_commutes_cnot` reproved with `grw` (generalized rewrite modulo `≈`), replacing the three `calc`/`gcongr` chains with `grw` lemma lists
- `docs/lean-api.md`: documented `grw` as the `rw`-modulo-`≈` tactic for `QState.Equiv`/`Circuit.Equiv` goals (descends via the `@[gcongr]` lemmas; `rw`/`simp`/`@[congr]` cannot)

---

## [2026-06-16]

### Changed
- `State/Type.lean`: ket notation now uses `❘` (U+2758, LIGHT VERTICAL BAR) instead of `⎸` (U+23B8); avoids Mathlib's `∣` divisibility token
- `Examples/RzCNOT.lean`: `rz_commutes_cnot` reproved entirely in the symbolic state layer via `Circuit.Equiv.basis_iff_tensor` (was matrix-level `basis_iff`)

### Added
- `Gate/StateActions.lean`: `RzGate_basis` — `Rz θ` acts on `❘a⟩` (`a : Fin (2^1)`) by phase `exp((2a-1)·iθ/2)`
- `State/Rewrite.lean`: `Circuit.Equiv.basis_iff_tensor` — `(j+k)`-qubit circuits are equivalent iff they agree on every factored basis state `❘a⟩ ⊗ₛ ❘b⟩`; `QState.basis_tensor_split` — `❘tensorIndexEquiv j k ⟨a,b⟩⟩ ≈ ❘a⟩ ⊗ₛ ❘b⟩`
- `State/Rewrite.lean` + `Circuit/Rewrite.lean`: `@[gcongr]` on all congruence lemmas (`QState.Equiv.apply_congr`/`add_congr`/`smul_congr`/`tensor_congr`, `Circuit.Equiv.seq_congr`/`par_congr`), enabling the `gcongr` tactic to descend `≈` goals through constructors to their leaves

---

## [2026-06-15] (2)

### Added
- `State/Type.lean`: `QState.apply` constructor; `HMul (Circuit n) (QState n) (QState n)` instance giving `C * s` notation
- `State/Semantics.lean`: `eval_apply` simp lemma (`eval (C * s) = Circuit.eval C * eval s`)
- `State/Rewrite.lean`: `QState.Equiv.apply_congr`; `Circuit.mapsExpr_iff` bridge (`C.mapsExpr s t ↔ C * s ≈ t`)

## [2026-06-15]

### Added
- `State/Type.lean`: `QState` inductive syntax tree, `castN`, `⊗ₛ` notation, `bit0`/`bit1`
- `State/Semantics.lean`: `QState.eval`, `IsNormalized`, `Circuit.mapsExpr`, `Circuit.maps_tensor`
- `State/Rewrite.lean`: `QState.Equiv` (`≈`), congruence lemmas, distributivity rules

### Changed
- Renamed `QState` (column-vector type) → `QVector`; renamed `QStateExpr` (symbolic syntax tree) → `QState`

---

## [2026-06-14]

### Added
- `docs/` directory with full library documentation (index, architecture, conventions, API reference, Lean API notes, references, examples)
- `CHANGELOG.md`

### Removed
- `notes/` planning wiki (superseded by `docs/`)

---

## Previous

### Changed
- Renamed `kronQMatrix` → `kron` throughout (`Basic/Tensor.lean`, all call sites)

### Added
- `Examples/QFT.lean`: `qftMatrix`, `isUnitary_qftMatrix`, `QFTGate_maps_ket`, `qftMatrix_one_eq_H`
- `IsUnitary.kron` in `Basic/Tensor.lean`; simplified `Circuit.eval_unitary`
- `Examples/GHZ.lean`: `ghzCircuit`, `ghzState`, `wf_ghzCircuit`, `ghzCircuit_prepares`
- `Examples/HadamardTransform.lean`: `hadamardTransform`, `uniformSuper`, `hadamardTransform_prepares`
- `Circuit.maps` / `Circuit.prepares` predicates in `Circuit/Semantics.lean`
- `Circuit.Equiv.basis_iff` in `Circuit/Rewrite.lean`
- `≈` notation for `Circuit.Equiv`; `*` / `+` / `1` notation for circuit composition
- `Examples/RzCNOT.lean`: `rz_commutes_cnot`
- `Basic/Hilbert.lean`: `QVector`, `ket`, `tensorState`, `act`, normalization and inner-product lemmas
- `Gate/Embed.lean`: `gateAt` with full algebra (`gateAt_mul`, `gateAt_one`, `gateAt_conjTranspose`, `gateAt_unitary`, `gateAt_comm_disjoint`)
- Unitarity proofs for `S`, `T`, `Rz`, `Rx`, `Ry`
- `prove_unitary` tactic macro in `Gate/Standard.lean`
- Circuit algebra layer: `Circuit.WF`, `Circuit.eval_unitary`, `seq_id_left/right`, `seq_assoc`, `par_assoc`, `interchange_law`
- `Basic/Tensor.lean`: `tensorIndexEquiv`, `kron`, `kron_mul`, `kron_conjTranspose`, `kron_one_one`, `kron_assoc`
- `Gate/Standard.lean`: `H`, `X`, `Y`, `Z`, `S`, `T`, `Rz`, `Rx`, `Ry`, `CNOT`, `CZ`, `SWAP`, `Toffoli`, `controlled`; unitarity proofs; circuit abbreviations
- `Basic/Matrix.lean`: `QMatrix`, `IsUnitary`, `IsUnitary.conj_mul`, `IsUnitary.mul`
- `Circuit/Type.lean`: `Circuit` inductive type, `Circuit.castN`
