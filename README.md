# QLean

A Lean 4 library for equational reasoning about quantum circuits, built on Mathlib.

QLean provides a typed circuit language (`QCircuit`: sequential `*`, parallel `⊗`, and
positional `embed` composition) with denotational matrix semantics, standard gates with
unitarity proofs, a symbolic state layer (`QState`) for rewriting modulo `≈`, and a
serializable `Program` IR that compiles to OpenQASM 3.0.

Worked examples in `Examples/` include Bell/GHZ state preparation, the n-qubit Hadamard
transform, Rz–CNOT commutation, and the quantum Fourier transform with a product-form
correctness proof and a verified OpenQASM emission path.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build QLean     # build the library
lake build Examples  # build the worked examples
```

The Lean toolchain is pinned in `lean-toolchain`; `elan` picks it up automatically.

## Documentation

Start at [docs/index.md](docs/index.md): overview, module map, quick start. Per-module API
reference in [docs/api.md](docs/api.md); design rationale in
[docs/architecture.md](docs/architecture.md); conventions (qubit ordering is **LSB-first**)
in [docs/conventions.md](docs/conventions.md).
