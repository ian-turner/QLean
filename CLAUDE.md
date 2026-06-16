# QLean

Lean 4 formalization of quantum computing circuits, built as a reusable library for equational reasoning about circuit identities and transformations.

## Project layout

| Path | Purpose |
|------|---------|
| `QLean/` | Lean 4 source (library root) |
| `Examples/` | Worked examples (GHZ, QFT, Hadamard transform, Rz–CNOT commutativity) |
| `docs/` | Library documentation — start at `docs/index.md` |
| `CHANGELOG.md` | Per-commit change log |
| `lakefile.toml` | Lake build config |
| `lean-toolchain` | Pinned Lean version |

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build QLean     # build the library
lake build           # also builds Examples
```

## Documentation

All durable project knowledge lives in `docs/`. Start at [`docs/index.md`](docs/index.md).

| File | Contents |
|------|----------|
| `docs/index.md` | Overview, module map, quick start |
| `docs/architecture.md` | Core type definitions and design rationale |
| `docs/conventions.md` | Qubit ordering, naming, `noncomputable`, `@[simp]` policy |
| `docs/api.md` | Per-module API reference |
| `docs/lean-api.md` | Discovered Mathlib API facts and pitfalls |
| `docs/references.md` | Related work and Mathlib modules |
| `docs/examples.md` | Annotated tour of `Examples/` |

### When to update `docs/`

Update only when there is a structural change that cannot be derived by reading the source:

- New module added → add a section to `docs/api.md`; update the module map in `docs/index.md`
- Public API changes (new exported def/theorem, renamed, removed) → update the relevant section in `docs/api.md`
- Design decision revised → update `docs/architecture.md`
- Mathlib API pitfall or actual lemma name discovered → add to `docs/lean-api.md`
- New example added → add a section to `docs/examples.md`

Do **not** update `docs/` for: internal proof cleanup, `@[simp]` attribute changes, helper lemma additions with no public-API impact, or in-progress scratch work.

### `CHANGELOG.md`

Add one entry per commit. Use categories `Added`, `Changed`, `Fixed`, `Removed`. Keep entries to one line each. Place new entries at the top under the current date.

## Design principles

See `docs/architecture.md` for the full rationale. Short version:

- Gates are raw `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`; unitarity is a separate predicate
- Circuits are a structured inductive type (`id / gate / seq / par`) with denotational semantics `eval : Circuit n → QMatrix n`
- Tensor product uses `kron` (reindexed `Matrix.kronecker`); the bridge is one equivalence in `Basic/Tensor.lean`
- `QVector n` is `Matrix (Fin (2^n)) (Fin 1) ℂ`; no `PiLp` coercions anywhere
