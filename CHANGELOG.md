# Changelog

One entry per commit. Newest first. Categories: `Added`, `Changed`, `Fixed`, `Removed`.

---

## [2026-06-28] (20)

### Added
- `QCircuit.embed` constructor (`Circuit/Type.lean`): positional embedding is now **first-class syntax** — `embed (qs : Fin k ↪ Fin n) (c : QCircuit k) : QCircuit n`, mirroring `seq`/`par`, so circuit-to-circuit passes can pattern-match where a sub-circuit is placed instead of seeing an opaque matrix. `eval`/`WF`/`eval_unitary` extended with the `embed` case (`eval (embed qs c) = embedₘ qs (eval c)`, `WF (embed qs c) = WF c`); `@[simp]` `eval_embed`/`wf_embed`
- `Basic/Embed.lean`: the two crux matrix laws — `embed_embed` (`embed qs (embed qs2 U) = embed (qs2.trans qs) U`, composing addressing maps, via `selectIdx_trans`) and `embed_kron_factor` (`embed qs (kron A B) = embed (lowEmb.trans qs) A * embed (highEmb.trans qs) B`, splitting a tensor across the new split-coordinate embeddings `lowEmb`/`highEmb`, via `selectIdx_lowEmb`/`selectIdx_highEmb` and the per-bit `tensor_symm_fst_bit`/`tensor_symm_snd_bit`); plus `embed_refl` (`embed (Embedding.refl) U = U`, via `selectIdx_refl`) and `kron_eq_embed` (`kron A B = embed (lowEmb) A * embed (highEmb) B`)
- `Circuit/Embed.lean` (new module, wired into `QLean.lean`): circuit-level `≈`-algebra of `embed` — `embed_gate`/`embed_id`/`embed_seq`/`embed_comp`/`embed_par_split`/`par_as_embed`/`embed_comm_disjoint` — plus the basis-ket action lemmas `embed_diag_action`/`embed_single_action` (lifting `embed_diag_mul_ket`/`embed_single_mul_ket` to the `QState` layer)
- `docs/lean-api.md`: `Function.Embedding.trans_apply` existence, `Fin.castAdd_injective`/`natAdd_injective` arg order + `val_*` lemmas, `push Not` needing `unfold` through a `def`-wrapped `∀`, and the anonymous-`Fin`-constructor / `omega` modulus-metavar pitfall

### Changed
- `Examples/QFT.lean`: migrated onto the first-class `embed` constructor — `qftCR` is now a `QCircuit`, `qftStageTop`/`swapLayer` place gates with `QCircuit.embed`, WF proofs are structural (dropped the by-hand `embed_unitary`), and `qftCR_apply`/`embedH_apply` are instances of `QCircuit.embed_diag_action`/`embed_single_action` (removed the bespoke `qftCR_mul_ket`); the bit-arithmetic/`qft_frac` correctness core is unchanged. `par` kept as its own constructor (not derived), with `embed_par_split` as the bridge
- `docs/`: `architecture.md` (new *Embedding as a circuit constructor* section; updated `QCircuit`/`eval`/`WF`), `api.md` (Embed/Type/Semantics + new `Circuit/Embed.lean` section), `index.md` (module map), `examples.md` (QFT)

---

## [2026-06-28] (19)

### Added
- `Examples/QFT.lean`: **product-form correctness of the QFT network** — `qftCore_correct n j : qftCore n * ❘j⟩ ≈ qftProductState n j` (Nielsen & Chuang eq 5.4), with `qftQubitState`/`qftProductState` the symbolic per-qubit/n-qubit targets. Proved in the `QState` syntax layer: `stage_apply` (cascade induction threading the rotation phase), `qftStageTop_apply` (single-stage → tensor), and a clean `qftCore_correct` induction; the matrix layer is touched only for atoms (`qftCR`/`crEntry`/`qftCR_mul_ket`, `crEntry_merge0/1`, `controlled_Rk_diag`, `H_row0/1`) and arithmetic (`qft_frac`/`digit_recon`, `prodMerge1`). Per-qubit phase is `e^{2πi·j/2^{m+1}}`. Swaps not yet folded into the correctness statement
- `State/Rewrite.lean`: `QState.one_smul`/`QState.smul_smul`/`QState.smul_add` — scalar-algebra `≈` lemmas recovering `MulAction`/`Module` rewriting in the symbolic layer (`QState.smul` is a bare `SMul`)

### Changed
- `Examples/QFT.lean`: factored the controlled-rotation gate into a named `qftCR m c`, so `qftStageTop` is `foldr (gate (qftCR …) * acc)` (was an inline `embed`); enables the correctness lemmas to name the per-gate action

---

## [2026-06-28] (18)

### Fixed
- `Examples/QFT.lean`: corrected the layer order in `qftStageTop` — the Hadamard must act *first* (be the rightmost `seq` factor), but the foldr placed it leftmost so the controlled rotations acted before it, computing the wrong unitary. Switched the foldr to prepend the rotations (`gate * acc`); `swapLayer` and the `wf_foldr_seq` helper updated to match. Found while setting up the correctness proof; WF was unaffected (order-independent)

### Added
- `Basic/EmbedState.lean`: top-qubit action bridge — `embedTop_mul_ket` (`embed (singleEmb (Fin.last m)) U * ket j = tensorState (ket j_low) (U * ket j_top)`), built on the index bridges `selectIdx_singleEmb_last`/`mergeBits_singleEmb_last` (relating `embed`'s `finFunctionFinEquiv` bit-addressing to `tensorIndexEquiv`'s tensor split) and the helper `mul_ket_one`. The clean entry point for proving correctness of circuits that process the most significant qubit
- `Basic/Hilbert.lean`: `tensorState_smul_right`, `tensorState_add_right` (right-factor linearity of `tensorState`, mirroring `tensorState_smul_left`)

---

## [2026-06-27] (17)

### Added
- `Gate/Standard.lean`: QFT phase gate `Rk k = diag(1, e^{2πi/2ᵏ})` (`R₁ = Z`, `R₂ = S`, `R₃ = T`) with `Rk_isDiag`, `isUnitary_Rk`, `RkGate`/`wf_RkGate`; plus `controlled_isDiag` (a controlled diagonal gate is diagonal — the basis for the QFT rotation layers)
- `Basic/Embed.lean`: `singleEmb`/`pairEmb` embedding constructors (`Fin 1 ↪ Fin n` at one qubit, `Fin 2 ↪ Fin n` at a distinct pair) with `@[simp]` apply lemmas — the addressing for embedded single-/two-qubit gates
- `Examples/QFT.lean`: the quantum Fourier transform circuit `qftCircuit n` (Nielsen & Chuang §5.1, Fig 5.1) — `qftStageTop`, recursive `qftCore`, qubit-reversal `swapLayer`, and `qftCircuit = swapLayer * qftCore`; well-formedness/unitarity (`wf_qftCircuit`, `isUnitary_qftCircuit`) via `embed_unitary` and the `wf_foldr_seq` helper; wired into `Examples.lean`

### Changed
- `Basic/EmbedState.lean`: factored the generic `isDiag_mul_ket` (any diagonal matrix acts on a basis ket by its eigenvalue) out of `embed_diag_mul_ket`, which is now one line (via `embed_isDiag` + `isDiag_mul_ket`), removing the duplicated off-diagonal-vanishing argument

---

## [2026-06-27] (16)

### Added
- `Basic/EmbedState.lean`: bridge from the `embed` matrix algebra to the state layer — `embed_diag_mul_ket` (a diagonal gate, embedded, acts on `ket i` by the scalar `U (selectIdx qs i) (selectIdx qs i)` with no superposition), `embed_isDiag`, the general `embed_mul_ket` (sum over `mergeBits` columns), the single-qubit `embed_single_mul_ket`, and the `mul_ket_apply` helper; wired into `QLean.lean`. Unblocks the long-range controlled-rotation layers of a QFT proof, which collapse to scalar phases
- `docs/lean-api.md`: `Matrix.IsDiag` import/dot-notation pitfall on `QMatrix`, and the `Fin.sum_univ_two`-vs-`Fin (2^1)` `rw`/`exact` pitfall

### Changed
- `Basic/Embed.lean`: promoted `mergeBits` and its round-trip lemmas (`mergeBits_bit_mem`, `mergeBits_bit_not_mem`, `selectIdx_mergeBits`, `agreeOff_mergeBits`, `mergeBits_selectIdx`) from `private` to public API — they are the address-reconstruction primitives the new state-action lemmas are phrased with

---

## [2026-06-26] (15)

### Added
- `Basic/Embed.lean`: positional gate embedding `embed (qs : Fin k ↪ Fin n) (U : QMatrix k) : QMatrix n` placing a gate on possibly non-adjacent/reordered qubits, with `selectIdx`/`AgreeOff` helpers, `index_ext_iff`, and the `embed_one`/`embed_mul`/`embed_conjTranspose`/`embed_unitary`/`embed_comm_disjoint` algebra — a fresh point-wise reimplementation of the removed `gateAt`, wired into `QLean.lean`

---

## [2026-06-18] (14)

### Changed
- Docstring/comment cleanup across `QLean/` and `Examples/`: condensed the verbose proof-walkthrough docstrings on the four `Examples/` theorems to a statement + brief approach, converted the `CNOT`/`CZ`/`SWAP`/`Toffoli`/`controlled` `--` comments to `/-- -/` docstrings for consistency, and dropped the `eval_castN` docstring self-reference and the `Toffoli` "deferred to v2" roadmap note

### Fixed
- `Gate/StateActions.lean`: corrected the `HGate_bit0`/`HGate_bit1` note that named `algebraMap_smul` (absent from the proof) — after `← Complex.ofReal_inv` the goal closes by defeq (ℂ-smul by `↑r` = ℝ-smul by `r`)

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
