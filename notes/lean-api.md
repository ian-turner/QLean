# Lean & Mathlib API Notes

Notes on Lean 4 / Mathlib APIs, known pitfalls, and useful lemmas for this project. Add entries as they are discovered; don't prune unless something is demonstrably wrong.

---

## EuclideanSpace and PiLp

`EuclideanSpace ℂ (Fin n)` is definitionally `PiLp 2 (fun _ : Fin n => ℂ)`. This is *not* the same as `Fin n → ℂ` at the definitional level. Consequences:

- **Indexing** requires `WithLp.equiv` or `PiLp.equiv` to coerce between the two.
- **Matrix-vector multiplication** must go through `Matrix.toEuclideanLin` rather than plain `Matrix.mulVec`.
- **Simp lemmas** `PiLp.smul_apply`, `PiLp.add_apply`, `WithLp.ofLp_sum` are essential for reducing coordinate goals.

**Strategy for QLean:** All `PiLp`-facing code lives in `Basic/PiLp.lean`. Every function that crosses between `EuclideanSpace` and raw coordinates goes through a small set of wrapper lemmas proved there. Higher-level code (gates, circuits) works only with `QMatrix` and never touches `PiLp` directly.

---

## Matrix.kronecker

`Matrix.kronecker` in Mathlib is an alias for `kroneckerMap (· * ·)`. The preferred notation is `A ⊗ₖ B` (requires `open scoped Kronecker`). Index type is `α × β`.

**Actual Mathlib names (verified against v4.30.0):**
- `Matrix.mul_kronecker_mul` — mixed product `(A*B) ⊗ₖ (A'*B') = (A ⊗ₖ A') * (B ⊗ₖ B')`; NOT `kronecker_mul` or `kroneckerMap_mul`
- `Matrix.one_kronecker_one` — `1 ⊗ₖ 1 = 1` (via `kroneckerMap_one_one`)
- `Matrix.conjTranspose_kronecker` — `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`; NOT `star_kronecker`
- `Matrix.kroneckerMap_assoc₁` — `reindex (Equiv.prodAssoc ...) ... ((A ⊗ₖ B) ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C)` when `mul_assoc` holds; this is the key lemma for `kronQMatrix_assoc`
- `Matrix.kroneckerMap_reindex` — `(reindex el em M) ⊗ₖ (reindex en ep N) = reindex (el.prodCongr en) (em.prodCongr ep) (M ⊗ₖ N)`
- `Matrix.kroneckerMap_reindex_left` / `_right` — one-sided variants

The gap: `A ⊗ₖ B` has index type `α × β`, but `QMatrix (j+k)` has index type `Fin (2^(j+k))`. Bridged once in `Gate/Tensor.lean` via `tensorIndexEquiv`. All downstream code uses `kronQMatrix` only.

**`reindex` lemmas — actual names (verified v4.30.0):**
- `Matrix.reindex_refl_refl` — `reindex (Equiv.refl _) (Equiv.refl _) A = A`; NOT `reindex_refl`
- `Matrix.reindex_trans` — `(reindex e₁ f₁).trans (reindex e₂ f₂) = reindex (e₁.trans e₂) (f₁.trans f₂)` ✓ exists
- `Matrix.reindexLinearEquiv_mul` — `reindex e e M * reindex e e N = reindex e e (M * N)` (square case); NOT `reindex_mul`
- `Matrix.reindexLinearEquiv_one` — `reindex e e 1 = 1`; NOT `reindex_one`
- `Matrix.conjTranspose_reindex` — `(reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ` (swaps row/col equiv); NOT `reindex_conjTranspose`

**Ordering pitfall:** `finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)` maps `(a, b) ↦ a.val * n + b.val` — MSB-first (a is the high component). `tensorIndexEquiv` must use `Equiv.prodComm` to put A in the low bits:
```lean
(Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [mul_comm, ← pow_add])))
```

---

## IsUnitary.conj_mul — proof path

`IsUnitary U := U * Uᴴ = 1`. To derive `Uᴴ * U = 1`, use:

```lean
theorem mul_eq_one_comm {M : Type*} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M} :
    a * b = 1 ↔ b * a = 1
```

So `IsUnitary.conj_mul h = mul_eq_one_comm.mp h` (one line).

**v4.30.0 name:** `mul_eq_one_comm` at the root namespace (NOT `Matrix.mul_eq_one_comm`, which is deprecated with a warning pointing to the root-level name). The instance `IsDedekindFiniteMonoid (Matrix n n ℂ)` is available since square matrices over a commutative ring are Dedekind-finite.

---

## Matrix.unitaryGroup

`Matrix.unitaryGroup (Fin n) ℂ` is the Σ-type `{ M : Matrix (Fin n) (Fin n) ℂ // M ∈ Matrix.unitaryGroup (Fin n) ℂ }`, where membership is `star M * M = 1`. The group axioms and `star`-ring structure are available for free.

**We avoid this in QLean** at the primary API level (see `design.md`), but it may be useful for constructing the gate group or proving abstract group-theoretic lemmas.

---

## finFunctionFinEquiv direction

**Verified in v4.30.0** — in `Mathlib.Algebra.BigOperators.Fin`:
```lean
finFunctionFinEquiv : {m n : ℕ} → (Fin n → Fin m) ≃ Fin (m ^ n)
```
For the 2-bit case used in `gateAt`: instantiate `m = 2` to get `(Fin n → Fin 2) ≃ Fin (2^n)`.
It is **LSB-first**: `f ↦ ∑ i, f(i) * 2^i.val`, so qubit 0 is the least significant bit.

`finCongr` is in `Mathlib.Data.Fin.SuccPred`:
```lean
finCongr : {n m : ℕ} → n = m → Fin n ≃ Fin m
```
With `@[simp] lemma finCongr_apply_coe (h : m = n) (k : Fin m) : (finCongr h k : ℕ) = k`.
This means `finCongr` just casts the underlying `ℕ` value; no bit permutation.

`finProdFinEquiv` is in `Mathlib.Logic.Equiv.Fin.Basic`:
```lean
finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)
```
Maps `(a, b) ↦ a.val * n + b.val` (a is the high component, MSB-first).

---

## prove_unitary macro

`Standard.lean` defines a `prove_unitary` tactic macro that closes concrete `IsUnitary M` goals after the gate and `IsUnitary` are unfolded:

```lean
macro "prove_unitary" : tactic =>
  `(tactic| ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one])
```

**Lean 4.30 macro pitfalls discovered during implementation:**
- `macro` cannot take a `private` modifier.
- `macro "X" : tactic => \`(tactic| t1; t2)` fails with *Application type mismatch* because `;` creates a `Lean.Parser.Tactic.seq1` node, which is not coercible to `TSyntax \`tactic`. Use `<;>` exclusively (produces `tactic_<;>_` nodes, which are properly registered).
- `macro` cannot appear inside a `noncomputable section`; place it before the section.
- Hadamard still requires its own proof (needs `ring_nf` + `sqrt2_sq_cast`).

---

## set_option … in + docstrings (Lean 4.30)

In Lean 4.30, placing a docstring `/-- … -/` *before* `set_option X Y in theorem …` is a parse error ("unexpected token 'set_option'; expected 'lemma'"). The docstring must immediately precede the declaration keyword.

**Fix:** put `set_option X Y in` *before* the docstring:
```lean
set_option maxHeartbeats 800000 in
/-- My theorem doc. -/
theorem foo := …
```

---

## Hadamard and √2

The Hadamard gate's entries are `1/√2`. Lean does not simplify `(1/√2)^2 = 1/2` without help. The `autoquantum` prototype uses a custom `sqrt2_sq_cast` lemma:
```lean
lemma sqrt2_sq_cast : (Real.sqrt 2 : ℂ)^2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  norm_cast
```
Prove this first in `Gate/Standard.lean`. The `H` unitarity proof then uses `simp [Matrix.mul_apply, sqrt2_sq_cast]` after `fin_cases i <;> fin_cases j`; `ring` or `norm_num` closes the resulting arithmetic goals. The `fin_cases` / `simp [Matrix.mul_apply]` approach used for permutation-matrix gates (CNOT, SWAP) does **not** close `H`'s unitarity goal without `sqrt2_sq_cast` in the simp set.

---

## norm_num and complex arithmetic

`norm_num` handles most concrete complex arithmetic. For goals involving `Real.sqrt`, `Complex.exp`, or trigonometric identities, use `ring_nf` to normalize first, then `norm_num` or explicit lemma rewrites.

---

## Fin arithmetic

`2^n` expressions in `Fin` indices require care:
- `Fin.val` arithmetic often requires `Nat.mod_eq_of_lt` to simplify.
- `decide` can close concrete index goals for small `n` (n ≤ 4 is fast; n = 5 may be slow).
- `omega` handles linear Nat/Int goals about `Fin.val`.

---

## noncomputable

All definitions involving `ℝ`, `ℂ`, `Real.sqrt`, `Complex.exp`, or `EuclideanSpace` must be `noncomputable`. This is expected and has no practical downside for a verification library. Mark everything `noncomputable` by default in files that use these types.
