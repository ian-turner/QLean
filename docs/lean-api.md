# Lean & Mathlib API Notes

Discovered facts about Lean 4 / Mathlib APIs: actual names, pitfalls, and useful lemmas. Add entries as they are found; update if a name changes.

---

## Matrix.kronecker

`Matrix.kronecker` is an alias for `kroneckerMap (· * ·)`. Preferred notation: `A ⊗ₖ B` (requires `open scoped Kronecker`). Index type is `α × β`.

**Actual names (verified against Mathlib v4.30.0):**
- `Matrix.mul_kronecker_mul` — mixed product `(A*B) ⊗ₖ (A'*B') = (A ⊗ₖ A') * (B ⊗ₖ B')`; NOT `kronecker_mul`
- `Matrix.one_kronecker_one` — `1 ⊗ₖ 1 = 1`
- `Matrix.conjTranspose_kronecker` — `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`; NOT `star_kronecker`
- `Matrix.kroneckerMap_assoc₁` — `reindex (Equiv.prodAssoc ...) ... ((A ⊗ₖ B) ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C)` when `mul_assoc` holds
- `Matrix.kroneckerMap_reindex` — `(reindex el em M) ⊗ₖ (reindex en ep N) = reindex (el.prodCongr en) (em.prodCongr ep) (M ⊗ₖ N)`

**`reindex` lemmas (verified v4.30.0):**
- `Matrix.reindex_refl_refl` — `reindex (Equiv.refl _) (Equiv.refl _) A = A`; NOT `reindex_refl`
- `Matrix.reindex_trans` — exists; composes two `reindex` calls
- `Matrix.reindexLinearEquiv_mul` — `reindex e e M * reindex e e N = reindex e e (M * N)`; NOT `reindex_mul`
- `Matrix.reindexLinearEquiv_one` — `reindex e e 1 = 1`; NOT `reindex_one`
- `Matrix.conjTranspose_reindex` — `(reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ` (swaps row/col equiv); NOT `reindex_conjTranspose`

**`finProdFinEquiv` ordering pitfall:** Maps `(a, b) ↦ a.val * n + b.val` — MSB-first. `tensorIndexEquiv` uses `Equiv.prodComm` to put A in the low bits:
```lean
(Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [mul_comm, ← pow_add])))
```

---

## `IsUnitary.conj_mul` proof path

`IsUnitary U := U * Uᴴ = 1`. To derive `Uᴴ * U = 1`:

```lean
mul_eq_one_comm.mp h
```

**v4.30.0 name:** `mul_eq_one_comm` at the root namespace (not `Matrix.mul_eq_one_comm`, which is deprecated). The `IsDedekindFiniteMonoid (Matrix n n ℂ)` instance is available since square matrices over a commutative ring are Dedekind-finite.

---

## `finFunctionFinEquiv` direction

**Verified in v4.30.0** — in `Mathlib.Algebra.BigOperators.Fin`:
```lean
finFunctionFinEquiv : {m n : ℕ} → (Fin n → Fin m) ≃ Fin (m ^ n)
```
For `(Fin n → Fin 2) ≃ Fin (2^n)`: instantiate `m = 2`. **LSB-first**: `f ↦ ∑ i, f(i) * 2^i.val`.

`finCongr` — in `Mathlib.Data.Fin.SuccPred`:
```lean
finCongr : {n m : ℕ} → n = m → Fin n ≃ Fin m
```
Casts the underlying `ℕ` value; no bit permutation. `@[simp] finCongr_apply_coe` reduces `(finCongr h k : ℕ) = k`.

---

## `prove_unitary` tactic macro

`Gate/Standard.lean` defines a macro that closes concrete `IsUnitary M` goals:

```lean
macro "prove_unitary" : tactic =>
  `(tactic| ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one])
```

**Lean 4.30 macro pitfalls:**
- `macro` cannot take a `private` modifier
- `;` inside `` `(tactic| t1; t2) `` creates a `Lean.Parser.Tactic.seq1` node that is not coercible to `TSyntax \`tactic`; use `<;>` exclusively
- `macro` cannot appear inside a `noncomputable section`; place it before the section
- Hadamard still requires its own proof (`ring_nf` + `sqrt2_sq_cast`)

---

## `set_option … in` + docstrings (Lean 4.30)

Placing a docstring `/-- … -/` before `set_option X Y in theorem …` is a parse error. The `set_option` must come first:

```lean
set_option maxHeartbeats 800000 in
/-- Docstring. -/
theorem foo := …
```

---

## Hadamard and √2

The Hadamard entries are `1/√2`. Lean needs a helper:

```lean
lemma sqrt2_sq_cast : (Real.sqrt 2 : ℂ)^2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  norm_cast
```

Prove this first in `Gate/Standard.lean`. The `H` unitarity proof uses `simp [Matrix.mul_apply, sqrt2_sq_cast]` after `fin_cases i <;> fin_cases j`.

---

## Fin arithmetic

- `2^n` expressions in `Fin` indices often need `Nat.mod_eq_of_lt` to simplify
- `decide` closes concrete index goals for small `n` (n ≤ 4 is fast)
- `omega` handles linear `ℕ`/`ℤ` goals about `Fin.val`; it cannot derive `2^j * 2^k = 2^(j+k)` — use `rw [pow_add]` first
- `ring` in Lean 4 treats variable exponents as opaque atoms; cannot derive `2^(j+k) = 2^j * 2^k`
