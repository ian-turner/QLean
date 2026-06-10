# References

Annotated bibliography for QLean. Focus on work directly relevant to Lean 4 quantum formalization, circuit algebra, and Mathlib APIs we use.

---

## Lean / Mathlib quantum formalization

**autoquantum** (`~/research/autoquantum`)
Predecessor project. Lean 4 + Mathlib formalization targeting LLM-assisted proof generation for a circuit-identity benchmark. Uses `EuclideanSpace`-based states, `Matrix.unitaryGroup` gates, and a flat `List`-based circuit type. See `notes/design.md` for what QLean inherits and where it diverges.

---

## Circuit algebra and categorical foundations

*To be filled in.* Key topics to search for:
- Dagger-compact categories and quantum circuits (Abramsky–Coecke)
- ZX-calculus (Coecke–Duncan) — a complete rewrite system for qubit circuits
- The interchange law for monoidal categories (directly motivates the `par`/`seq` design)

---

## Mathlib modules of interest

- `Mathlib.LinearAlgebra.Matrix.ToLin` — `Matrix.toEuclideanLin` and the PiLp bridge
- `Mathlib.LinearAlgebra.Matrix.Kronecker` — `Matrix.kronecker` and mixed-product identities
- `Mathlib.Analysis.InnerProductSpace.PiL2` — `EuclideanSpace`, norm, inner product
- `Mathlib.GroupTheory.GroupAction.Matrix` — `Matrix.unitaryGroup` as a group
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — `Complex.exp` on the unit circle, useful for phase rotation gates
- `Mathlib.Algebra.BigOperators.Finprod` — sum/product over `Fin n`, needed for state normalization proofs
