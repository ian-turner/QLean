# QLean Wiki

Central index for durable project notes. Keep entries here stable and design-level; do not record transient proof attempts, session-specific debugging, or benchmark scores.

## Project

- **Goal:** A clean, reusable Lean 4 library for equational reasoning about quantum circuits.
- **Approach:** Structured circuit type with denotational matrix semantics; equational rewriting at the circuit-syntax level, discharged by matrix algebra.
- **Non-goal:** A benchmark tool or LLM training pipeline (see `~/research/autoquantum` for that).

## Topics

### Architecture

- [Design Plan](design.md) — Module layout, key type definitions, design decisions and their rationale

### Lean Formalization

- [Lean & Mathlib API Notes](lean-api.md) — Useful lemmas, known pitfalls (PiLp, EuclideanSpace, kronecker), simp-set guidance

### Research

- [References](references.md) — Related Lean quantum libraries, foundational papers, relevant Mathlib modules
