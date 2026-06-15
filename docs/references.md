# References

Related work and Mathlib modules of interest.

---

## Circuit algebra and categorical foundations

- **Dagger-compact categories** — Abramsky & Coecke; foundational framework for quantum circuits as morphisms in a compact closed category with dagger
- **ZX-calculus** — Coecke & Duncan; a complete graphical rewrite system for qubit circuits; motivates the structural rewrite rules in `Circuit/Rewrite.lean`
- **Interchange law** — motivates the `par`/`seq` inductive type design; the law `(a * b) + (c * d) ≈ (a + c) * (b + d)` is the monoidal category exchange law

---

## Mathlib modules used

- `Mathlib.LinearAlgebra.Matrix.Kronecker` — `Matrix.kronecker` and mixed-product identities
- `Mathlib.Algebra.BigOperators.Fin` — `finFunctionFinEquiv`, `Fin.sum_univ_two`, etc.
- `Mathlib.Logic.Equiv.Fin` — `finProdFinEquiv`, `finCongr`
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — `Complex.exp` on the unit circle; used by rotation gates
- `Mathlib.Algebra.Ring.GeomSum` — geometric sum formula; used in `QFT.lean`'s unitarity proof
