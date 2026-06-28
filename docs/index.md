# QLean

A Lean 4 library for equational reasoning about quantum circuits, built on Mathlib.

## What it is

QLean provides a typed circuit language with denotational matrix semantics, standard gates with unitarity proofs, and tools for proving that two circuits compute the same unitary.

- `QCircuit n` — structured inductive type with sequential (`*`), parallel (`⊗`), and positional (`embed`) composition
- `eval : QCircuit n → QMatrix n` — denotational semantics (matrix product and Kronecker product)
- `QCircuit.Equiv` / `≈` — circuit equality up to matrix equality
- State-level layer: `QVector n`, `ket`, `tensorState`, `QState` symbolic state expressions

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
    Hilbert.lean      — QVector, ket, tensorState, act
    EmbedState.lean   — bridge: embed acting on basis kets (embed_diag_mul_ket, embed_single_mul_ket)
  Gate/
    Standard.lean     — H, X, Y, Z, S, T, Rz, Rx, Ry, Rk, CNOT, CZ, SWAP, Toffoli, controlled;
                        unitarity proofs; QCircuit abbreviations (HGate, CNOTGate, …);
                        QVector-level gate action lemmas (X_ket_zero, H_ket_zero, CNOT_ket_pair, …)
    StateActions.lean — symbolic gate actions: XGate_bit0, HGate_bit0, CNOTGate_basis_tensor, …
  Circuit/
    Type.lean         — QCircuit inductive type (id/gate/seq/par/embed), castN
    Semantics.lean    — eval, QCircuit.WF, QCircuit.eval_unitary (all covering the embed case)
    Rewrite.lean      — QCircuit.Equiv, structural rewrite rules, interchange law;
                        QCircuit.* actions on states + symbolic-state criteria
                        (apply_state, basis_iff_state, equiv_iff_all_states, basis_iff_tensor)
    Embed.lean        — circuit-level embed algebra (embed_gate/id/seq/comp/par_split/comm_disjoint)
                        and basis-ket action lemmas (embed_diag_action, embed_single_action)
  State/
    Type.lean         — QState inductive type, castN, ⊗ notation, bit0/bit1
    Semantics.lean    — QState.eval, QState.IsNormalized
    Rewrite.lean      — QState.Equiv, congruence/distributivity lemmas, tensor/basis splits
Examples/
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
```

## Quick start

```lean
import QLean
open QLean

-- 2-qubit Bell circuit: H on qubit 0, then CNOT
def bellCircuit : QCircuit (1 + 1) := (HGate ⊗ (1 : QCircuit 1)) * CNOTGate

theorem wf_bellCircuit : QCircuit.WF bellCircuit := by
  simp [bellCircuit, isUnitary_H, isUnitary_CNOT]
```

For worked examples, see [examples.md](examples.md).
