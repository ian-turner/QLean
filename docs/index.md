# QLean

A Lean 4 library for equational reasoning about quantum circuits, built on Mathlib.

## What it is

QLean provides a typed circuit language with denotational matrix semantics, standard gates with unitarity proofs, and tools for proving that two circuits compute the same unitary.

- `QCircuit n` — structured inductive type with sequential (`*`), parallel (`⊗`), and positional (`embed`) composition
- `eval : QCircuit n → QMatrix n` — denotational semantics (matrix product and Kronecker product)
- `QCircuit.Equiv` / `≈` — circuit equality up to matrix equality
- State-level layer: `QVector n`, `ket`, `tensorState`, `QState` symbolic state expressions
- `Program n` — serializable named-gate IR (`Prim` basis gates, symbolic `Angle`s, qubit indices); `denote : Program n → QCircuit n` bridges to semantics, `Program.toQASM` compiles to OpenQASM 3.0

## What it is not

- Not computational — all definitions are `noncomputable`
- No measurement, mixed states, density matrices, or noise models

## Module map

```
QLean/
  Basic/
    Matrix.lean       — QMatrix, IsUnitary, core lemmas
    Tensor.lean       — kron (reindexed Kronecker product) and its algebra
    Embed.lean        — embed (gate on selected, possibly non-adjacent qubits); embed_* algebra,
                        composition (embed_embed) + tensor split (embed_kron_factor), lowEmb/highEmb
    Hilbert.lean      — QVector, ket, tensorState
    EmbedState.lean   — bridge: embed acting on basis kets (embed_diag_mul_ket, embed_single_mul_ket)
  Gate/
    Standard.lean     — H, X, Y, Z, S, T, Tdg, Rz, Rx, Ry, Rk, sqrtX, CNOT, CNOTRev, CZ, SWAP,
                        sqrtSWAP, Toffoli, CCZ, Fredkin, controlled; unitarity proofs;
                        QCircuit abbreviations (HGate, CNOTGate, …);
                        QVector-level gate action lemmas (X_ket_zero, CNOT_ket_pair,
                        controlled_tensorState_zero/one, SWAP_tensorState, Toffoli_ket_triple, …)
    StateActions.lean — symbolic gate actions: XGate_bit0, HGate_bit0, CNOTGate_basis_tensor,
                        control-splits (ControlledGate_zero/one, CNOTGate_zero/one, CZGate_*),
                        SWAPGate_tensor, ToffoliGate/CCZGate_basis_tensor, FredkinGate_zero/one, …
    Tactics.lean      — circuit_eq: entrywise decision tactic for concrete circuit identities
                        (escape hatch for irreducible atoms; prefer grw/state-layer proofs)
  Circuit/
    Type.lean         — QCircuit inductive type (id/gate/seq/par/embed), castN
    Semantics.lean    — eval, QCircuit.WF, QCircuit.eval_unitary (all covering the embed case)
    Rewrite.lean      — QCircuit.Equiv, structural rewrite rules, interchange law;
                        QCircuit.* actions on states + symbolic-state criteria
                        (apply_state, basis_iff_state, equiv_iff_all_states, basis_iff_tensor)
    Embed.lean        — circuit-level embed algebra (embed_gate/id/seq/comp/par_split/comm_disjoint)
                        and basis-ket action lemmas (embed_diag_action, embed_single_action)
  Program/            — serializable named-gate IR; compiles to OpenQASM
    Angle.lean        — Angle := ℚ multiples of π; denote (· π), toQASM ("pi/4")
    Basis.lean        — Prim basis-gate enum; arity/matrix/isUnitary/toQASM
    Type.lean         — Program (id/prim/seq), denote → QCircuit, denote_unitary, ofList, relabel
    QASM.lean         — Program.toQASM : Program n → String (OpenQASM 3.0)
    Rewrite.lean      — denote_foldr_seq, denote_relabel (re-addressing), embed_congr
  State/
    Type.lean         — QState inductive type, ⊗ and ❘i⟩ notation
    Semantics.lean    — QState.eval, QState.IsNormalized
    Rewrite.lean      — QState.Equiv, congruence/distributivity lemmas, tensor/basis splits
Examples/
  PauliAlgebra.lean   — Pauli relations: X²=Y²=Z²=H²=1, XY=iZ (and cyclic), anticommutation,
                        Y=iXZ, H=(X+Z)/√2 (N&C Ex 2.41–2.43)
  CliffordConjugation.lean — HXH=Z, HZH=X, HYH=−Y (N&C Ex 4.13); T²=S, S²=Z, T⁸=1, X=HS²H
  SwapFromCNOT.lean   — SWAP = CNOT·CNOTRev·CNOT (N&C Fig 1.7); SWAP² = 1
  CNOTCZ.lean         — CNOT ↔ CZ Hadamard bridge, CZ symmetry, (H⊗H)-reversal, polarity flip
  CNOTPauli.lean      — CNOT–Pauli conjugation table (N&C Ex 4.31, six identities)
  ControlledConj.lean — C-(UAU†) = (1⊗U)·C-A·(1⊗U†); C-S = (T⊗T)·CNOT·(1⊗T†)·CNOT
  RzPlus.lean         — sequential Z-rotations fuse: Rz(φ)·Rz(θ) ≈ Rz(θ+φ)
  RzCNOT.lean         — Rz(θ) commutes with CNOT on the control qubit
  HadamardTransform.lean — n-qubit Hadamard transform prepares the uniform superposition
  BellState.lean      — H then CNOT prepares the entangled Bell state |Φ⁺⟩
  GHZState.lean       — H then a CNOT cascade prepares the (n+1)-qubit GHZ state
  QFT.lean            — quantum Fourier transform circuit (qftCircuit n) with swap layer, built
                        from the first-class `embed` constructor; well-formedness/unitarity +
                        product-form correctness of qftCore (qftCore_correct, in the QState layer;
                        swaps not yet folded in)
```

See [api.md](api.md) for per-module detail.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build QLean     # build the library
lake build           # also builds Examples
lake exe qft         # print the verified 8-qubit QFT as OpenQASM 3.0
```

## Quick start

```lean
import QLean
open QLean

-- 2-qubit Bell circuit: H on qubit 0, then CNOT (the rightmost factor acts first)
def bellCircuit : QCircuit (1 + 1) := CNOTGate * (HGate ⊗ (1 : QCircuit 1))

theorem wf_bellCircuit : QCircuit.WF bellCircuit := by
  simp [bellCircuit, isUnitary_H, isUnitary_CNOT]
```

For worked examples, see [examples.md](examples.md).
