# QLean

A Lean 4 library for equational reasoning about quantum circuits, built on Mathlib.

## What it is

QLean provides a typed circuit language with denotational matrix semantics, standard gates with unitarity proofs, and tools for proving that two circuits compute the same unitary.

- `Circuit n` — structured inductive type with sequential (`*`) and parallel (`+`) composition
- `eval : Circuit n → QMatrix n` — denotational semantics (matrix product and Kronecker product)
- `Circuit.Equiv` / `≈` — circuit equality up to matrix equality
- State-level layer: `QVector n`, `ket`, `tensorState`, `Circuit.maps`, `Circuit.prepares`

## What it is not

- Not computational — all definitions are `noncomputable`
- No measurement, mixed states, density matrices, or noise models

## Module map

```
QLean/
  Basic/
    Matrix.lean       — QMatrix, IsUnitary, core lemmas
    Tensor.lean       — kron (reindexed Kronecker product) and its algebra
    Hilbert.lean      — QVector, ket, tensorState, act
  Gate/
    Standard.lean     — H, X, Y, Z, S, T, Rz, Rx, Ry, CNOT, CZ, SWAP, Toffoli, controlled;
                        unitarity proofs; Circuit abbreviations (HGate, CNOTGate, …);
                        QVector-level gate action lemmas (X_ket_zero, H_ket_zero, CNOT_ket_pair, …)
    Embed.lean        — gateAt: embed any k-qubit gate at chosen positions in an n-qubit system
    StateActions.lean — symbolic gate actions: XGate_bit0, HGate_bit0, CNOTGate_basis_tensor, …
  Circuit/
    Type.lean         — Circuit inductive type, castN
    Semantics.lean    — eval, Circuit.WF, Circuit.maps, Circuit.prepares
    Rewrite.lean      — Circuit.Equiv, structural rewrite rules, interchange law
  State/
    Type.lean         — QState inductive type, castN, ⊗ₛ notation, bit0/bit1
    Semantics.lean    — eval, IsNormalized, Circuit.mapsExpr, Circuit.maps_tensor
    Rewrite.lean      — QState.Equiv, congruence lemmas, distributivity rules;
                        Circuit.Equiv.basis_iff_state, equiv_iff_all_states
Examples/
  RzCNOT.lean         — Rz(θ) commutes with CNOT on the control qubit
  HadamardTransform.lean — n-qubit Hadamard transform prepares the uniform superposition
  GHZ.lean            — chain GHZ circuit prepares (|0…0⟩ + |1…1⟩)/√2
  QFT.lean            — QFT matrix, unitarity proof, QFT₁ = H
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
def bellCircuit : Circuit 2 := (HGate + (1 : Circuit 1)) * CNOTGate

theorem wf_bellCircuit : Circuit.WF bellCircuit := by
  simp [bellCircuit, isUnitary_H, isUnitary_CNOT]
```

For worked examples, see [examples.md](examples.md).
