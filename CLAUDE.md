# QLean

Lean 4 formalization of quantum computing circuits, built as a reusable library for equational reasoning about circuit identities and transformations.

## Project layout

| Path | Purpose |
|------|---------|
| `QLean/` | Lean 4 source (library root, once initialized) |
| `lakefile.lean` | Lake build config |
| `lean-toolchain` | Pinned Lean version |
| `notes/` | Durable project wiki — see `notes/home.md` |

## Build (once initialized)

```bash
lake exe cache get
lake build QLean
```

## Wiki

All durable project knowledge — design decisions, API notes, references — lives in `notes/`. Start at [`notes/home.md`](notes/home.md). Do not put transient proof-attempt details or benchmark-specific notes into the wiki; those belong in commit messages or conversation context.

**When to update the wiki:**
- A design decision is made or revised → update `notes/design.md`
- A Mathlib API pitfall or useful lemma is discovered → add to `notes/lean-api.md`
- A new reference or related work is found → add to `notes/references.md`

## Design principles

See `notes/design.md` for the full rationale. Short version:

- Gates are raw `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`; unitarity is a separate predicate
- Circuits are a structured inductive type (`id / gate / seq / par`) with a denotational semantics `eval : Circuit n → QMatrix n`
- Tensor product uses `Matrix.kronecker`; parallel composition (`par`) and Kronecker product are related by one key coherence lemma
- All `PiLp` coercions are insulated in `QLean.Basic.PiLp`; higher-level code never sees them
