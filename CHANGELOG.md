# Changelog

One entry per commit. Newest first. Categories: `Added`, `Changed`, `Fixed`, `Removed`.

---

## [2026-06-16]

### Changed
- `State/Type.lean`: ket notation now uses `❘` (U+2758, LIGHT VERTICAL BAR) instead of `⎸` (U+23B8); avoids Mathlib's `∣` divisibility token

### Added
- `Gate/StateActions.lean`: `RzGate_basis` — `Rz θ` acts on `❘a⟩` (`a : Fin (2^1)`) by phase `exp((2a-1)·iθ/2)`

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
