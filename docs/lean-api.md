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

## `push_neg` deprecated → `push Not` (v4.30.0)

`push_neg at h` now emits a deprecation warning; the replacement is `push Not at h` (the
general `push` tactic with the `Not` head). Same behaviour: `¬ ∀ x, P x → Q x` becomes
`∃ x, P x ∧ ¬ Q x`, hypotheses of implications are left positive.

---

## `congr 1` does not split through the `finFunctionFinEquiv.symm` coercion

`finFunctionFinEquiv.symm s a` is `(⇑(Equiv.symm finFunctionFinEquiv) s) a` — a `DFunLike`
coercion applied to an argument. `congr 1` on `finFunctionFinEquiv.symm s x = finFunctionFinEquiv.symm s y`
fails to reduce it to `x = y` (it stalls on the coercion rather than peeling the outer
application). Instead, rewrite the argument directly with a proof `x = y`:

```lean
have hca : (⟨a, rfl⟩ : ∃ a', qs a' = qs a).choose = a :=
  qs.injective (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', qs a' = qs a))
rw [dif_pos ⟨a, rfl⟩, hca]
```

To compare two `finFunctionFinEquiv`-encoded indices, go the other way: `apply
finFunctionFinEquiv.symm.injective` then `funext` reduces the goal to a per-bit equality.

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

## `QCircuit.eval` namespace placement

Defining `def eval` inside `namespace QLean` (but outside `namespace QCircuit`) does not create `QCircuit.eval` as a true name — it only creates `QLean.eval`. Dot notation `c.eval` resolves to the wrong function, and `open QCircuit` does not expose it.

**Fix:** Move `def eval` (and its `@[simp]` lemmas) into an explicit `namespace QCircuit ... end QCircuit` block inside `namespace QLean`. This makes `QLean.QCircuit.eval` the canonical qualified name.

**Side effect of the wrong approach:** Using an `abbrev QCircuit.eval := eval` alias inside `namespace QLean` with `open QCircuit` in scope causes a termination-check failure because the body's `eval` resolves to the `abbrev` itself.

---

## ℝ → ℂ scalar coercions in `SMul` proofs

`((r : ℝ)⁻¹ : ℂ)` elaborates as `(Complex.ofReal r)⁻¹` (ℂ-inverse after coercion), NOT as `Complex.ofReal (r⁻¹)` (ofReal of ℝ-inverse). These are equal by `Complex.ofReal_inv` but are NOT definitionally equal — `rfl` fails.

When a QVector lemma uses `SMul ℝ (QVector n)` (e.g. `H_ket_zero`) but the goal has a ℂ-smul scalar of the form `(↑r)⁻¹`, the proof pattern is:

```lean
simp only [..., ← Complex.ofReal_inv]
-- (↑r)⁻¹ → ↑(r⁻¹); now ↑(r⁻¹) • v = r⁻¹ • v is definitional
exact H_ket_zero
```

`algebraMap_smul` is not needed because after `← Complex.ofReal_inv`, the remaining `↑(r⁻¹) • v = r⁻¹ • v` is definitionally true.

---

## `tensorState (ket a) (ket b)` vs `ket (tensorIndexEquiv ⟨a, b⟩)` form

Lemmas like `CNOT_ket_pair` are stated in `ket (tensorIndexEquiv ...)` form, but `QState.eval_tensor` + `eval_basis` produce `tensorState (ket a) (ket b)`. Bridge with `ket_tensorState` in the simp set:

```lean
simp only [..., ket_tensorState]
exact CNOT_ket_pair a b
```

`ket_tensorState` fires on both the LHS and RHS tensor expressions, converting both to `ket (tensorIndexEquiv ...)` form.

---

## Fin arithmetic

- `2^n` expressions in `Fin` indices often need `Nat.mod_eq_of_lt` to simplify
- `decide` closes concrete index goals for small `n` (n ≤ 4 is fast)
- `omega` handles linear `ℕ`/`ℤ` goals about `Fin.val`; it cannot derive `2^j * 2^k = 2^(j+k)` — use `rw [pow_add]` first
- `ring` in Lean 4 treats variable exponents as opaque atoms; cannot derive `2^(j+k) = 2^j * 2^k`

---

## When a ket `❘i⟩` needs a `: QState n` annotation

`❘i⟩` is `QState.basis (i : Fin (2^n))`. The qubit count `n` must be pinned **before** the index is elaborated, so the rule depends on the index, not the position:

- **Bare-numeral index** (`❘0⟩`, `❘1⟩`): `0`/`1` need `OfNat (Fin (2^n)) _`, which is stuck while `n` is a metavariable. The numeral must get `n` from an explicit annotation or a *propagated expected type*. It is **stuck** — and so needs `(❘0⟩ : QState n)` — exactly at the first position Lean elaborates with `n` still unknown: the gate-applied ket in `C * ❘0⟩ ≈ …` (the `HMul`/`≈` constraints that would fix `n` are postponed past the `OfNat` search), and the LHS of a basis split like `ket_zero_tensor`.
- **Variable index already typed** (`❘a⟩` with `a : Fin (2^1)`, or `❘tensorIndexEquiv j k ⟨a,b⟩⟩`): `n` unifies from the index's `Fin (2^·)` type, so **no annotation is ever needed** — neither on the LHS, RHS, nor inside a `calc`.

Once the first ket pins `n`, everything downstream infers it for free:
- The **RHS of `≈`** infers `n` from the LHS (the relation is homogeneous `QState n`), so RHS kets are always bare — even bare numerals.
- A ket in a **`def` body** infers `n` from the declared return type (`def plusState : QState 1 := … • (❘0⟩ + ❘1⟩)`).

**Two unification caveats** (annotation still required even when a result type is known):
- A tensor *split* `QState (j+k)` does not solve `?a + ?b =?= j + k` uniquely, so **both** factors of `ket_zero_tensor` need `: QState j` / `: QState k` (and the numeral LHS needs `: QState (j+k)`).
- `tensor_assoc` needs an outer `(… : QState (j + (k+1)))` to bridge the `(j+k)+1 = j+(k+1)` defeq, because `j + ?b =?= (j+k)+1` is not solvable by unification.

---

## Rewriting modulo `QState.Equiv` / `QCircuit.Equiv` — use `grw`, not `rw`/`simp`

`QState.Equiv s t` is *defined* as `eval s = eval t` (likewise `QCircuit.Equiv`). So an action/congruence lemma such as `QCircuit.seq_action : (c₁*c₂)*s ≈ c₁*(c₂*s)` is really `eval ((c₁*c₂)*s) = eval (c₁*(c₂*s))` — an `Eq` whose LHS pattern is an `eval (…)` application.

**Why `rw`/`simp` fail.** `rw` and `simp` only do congruence rewriting for `=`/`↔`, and they match a lemma's LHS against subterms. Since the only `eval (…)` subterms in a goal `eval s = eval t` are the two **outermost** ones, these lemmas can only rewrite the whole expression — never a nested sub-state (e.g. the `1 * ❘b⟩` inside `CNOT * ((Rz θ * ❘a⟩) ⊗ (1 * ❘b⟩))`). `rw [h]` for `h : a ≈ b` unfolds `≈` to the `Eq` of `.eval`s and then can't find an `.eval` subterm in the still-folded goal. `simp [h]` rewrites only at the top level, then stalls. A `@[congr]` lemma can't fix this either: Lean requires `@[congr]` conclusions to be `Eq`/`Iff`, and our congruence lemmas conclude in `≈`.

**Use `grw` (Mathlib's generalized rewrite).** `grw [h₁, h₂, …]` is `rw [h₁, h₂, …]` modulo `≈`: it rewrites subterms under a relation using that relation's `@[gcongr]` congruence lemmas to descend. The congruence lemmas here — `QState.Equiv.apply_congr`/`add_congr`/`smul_congr`/`tensor_congr` and `QCircuit.Equiv.seq_congr`/`par_congr` — are all `@[gcongr]`, so `grw` already works on both relations with no extra setup. Behaviour to know:
- Each list entry does **one outermost rewrite** (no fixpoint iteration), and `grw` **errors if a listed lemma matches nothing** — exactly like `rw`. So a `grw` list is a directed derivation, not a grab-bag.
- Supports `grw [← lem]`, hypotheses (`grw [hφ]`), and lemmas with arguments (`grw [rz_phase b]`).
- One `grw` can rewrite *both sides* of an `≈` goal to a common form and then close it by `rfl`.
- A `QCircuit.Equiv` fact can be rewritten inside a `QState` goal if the bridge `QCircuit.Equiv.apply_state` is tagged `@[gcongr]` (it is not, by default — tag it if needed).

This replaces the old `calc`/`Trans` + `gcongr` scaffolding for directional `≈` reductions. See `Examples/RzCNOT.lean`, where each derivation step is a single `grw` list.

**Still useful:**
- `gcongr` on its own for a pure congruence step (relate `C[s]` and `C[t]` when only a sub-state differs), auto-closing matching leaves by `rfl`/`assumption`.
- To finish at the matrix level instead, push `eval` all the way in with the structural simp lemmas (`eval_apply`, `eval_tensor`, `eval_basis`, `QCircuit.eval_seq/par/gate/id`) and then chain genuine `Matrix`/`QVector` `Eq` lemmas — that is what `QCircuit.Equiv.basis_iff` proofs do.

---

## `Matrix.IsDiag`

`Matrix.IsDiag (A : Matrix n n α) : Prop := ∀ ⦃i j⦄, i ≠ j → A i j = 0`. Lives in
`Mathlib.LinearAlgebra.Matrix.IsDiag` (import it explicitly). Comes with `IsDiag.add`/`.smul`/
`.mul`/`.conjTranspose`/`.neg` etc.

**Dot-notation pitfall.** `QMatrix n` is `abbrev`-reduced to the function type `Fin (2^n) → Fin (2^n) → ℂ`,
so `U.IsDiag` resolves to the (nonexistent) `Function.IsDiag` and errors with
`Invalid field 'IsDiag': … does not contain 'Function.IsDiag'`. Write `Matrix.IsDiag U`
(and `Matrix.IsDiag (embed qs U)`) in full — the explicit form unifies `QMatrix` with `Matrix … … …`
fine; only the projection notation breaks.

---

## `Fin.sum_univ_two` against a `Fin (2^1)` binder

`Fin.sum_univ_two : ∑ i : Fin 2, f i = f 0 + f 1` (and `_three`, etc.) will **not `rw`** against a
sum over `Fin (2^1)` — `rw` uses keyed/syntactic matching and does not reduce the numeral `2^1` to
`2`, so it reports "did not find an occurrence of the pattern". Full unification *does* reduce it,
so close the goal with `exact Fin.sum_univ_two _` (or `simp [Fin.sum_univ_two]`) instead of `rw`.
Same trick applies wherever a `Fin (2^k)` index must defeq-collapse to a concrete `Fin m`.

---

## `Function.Embedding` composition (v4.30.0)

`Function.Embedding.trans (f : α ↪ β) (g : β ↪ γ) : α ↪ γ` is `⟨g ∘ f, _⟩`, so `(f.trans g) a = g (f a)`:
- `Function.Embedding.trans_apply` **exists** (auto-generated by `@[simps]` on `trans`) — usable with `rw`/`simp`.
- `Function.Embedding.coe_trans : ⇑(f.trans g) = ⇑g ∘ ⇑f` also exists.
- The per-element equation is definitionally `rfl`, so a local `rfl` helper works too if `trans_apply` will not fire on a given goal shape.

---

## `Fin.castAdd`/`natAdd` injectivity and value lemmas

- `Fin.castAdd_injective (m n) : Injective (@Fin.castAdd m n)` — for `Fin.castAdd k : Fin j → Fin (j+k)` use `Fin.castAdd_injective j k`.
- `Fin.natAdd_injective (m n) : Injective (Fin.natAdd n : Fin m → _)` — **arg-order gotcha**: for `Fin.natAdd j : Fin k → Fin (j+k)` use `Fin.natAdd_injective k j` (args swapped relative to `castAdd`).
- Values: `Fin.val_castAdd : (castAdd m i : ℕ) = i`, `Fin.val_natAdd : (natAdd n i : ℕ) = n + i` (both `@[simp]`, `rfl`). The `Fin.coe_castAdd`/`Fin.coe_natAdd` spellings are **deprecated** (2025-11-21) — use `val_*`.
- Split a `Fin (j+k)` position into the two halves with `Fin.addCases (motive := …) (fun a => …) (fun b => …) c` (pass `motive` explicitly so HO-unification does not stall).

---

## `push Not` cannot see through a `def`-wrapped `∀`

`AgreeOff qs i j` is a `def` (`∀ l, … → …`). `push Not at h` reports "made no progress" on `h : ¬ AgreeOff qs i j` because the `∀` is hidden behind the definition. `unfold AgreeOff at h` **first**, then `push Not at h` produces the `∃ l, … ∧ …` witness. (Applies to any negated `def`-wrapped quantifier.)

---

## Anonymous `Fin` constructor + `omega` can capture a modulus metavar

Writing `⟨i.val, by … omega⟩` where the expected `Fin ?N` modulus `?N` is still a metavariable is dangerous: `omega` may **instantiate `?N`** from a bound it has on hand (e.g. `i.isLt : i.val < n/2`), giving the term type `Fin (n/2)` instead of the intended `Fin n` — surfacing later as a mismatched `HMul (QCircuit (n/2)) …` instance failure. This bit the QFT `swapLayer` when its gate moved from `gate (embed …)` (codomain fixed early) to the `QCircuit.embed` constructor (codomain fixed only by the outer `* acc`). Fix: pin the modulus at the constructor — `(⟨i.val, by … omega⟩ : Fin n)`.

## A `Namespace.foo` definition body auto-opens `Namespace`

`def Prim.matrix : (g : Prim) → QMatrix g.arity | H => H | …` elaborates its body with the
`Prim` namespace open, so unqualified RHS names like `H`, `Z`, `SWAP`, `Rk` resolve to the
**constructors** `Prim.H`/`Prim.Z`/… (which shadow the gates of the same name from
`Gate/Standard.lean`), giving "type mismatch: has type `Prim` but expected `QMatrix …`".
Fix: `_root_`-qualify the intended gate — `| H => _root_.QLean.H`. (The pattern side is fine;
there the names are unambiguously the inductive's constructors.)

## A `def` with a dependent return motive does not reduce in another def's match branches

`Prim.matrix : (g : Prim) → QMatrix g.arity` has a return type depending on `g`. Proving
`Prim.isUnitary : (g) → IsUnitary g.matrix` in **term-mode** by `| H => isUnitary_H` fails:
the branch's expected type `IsUnitary (Prim.matrix Prim.H)` is not reduced to `IsUnitary H`, so
`isUnitary_H : IsUnitary H` mismatches. Prove it in **tactic mode** instead — `cases g` then one
`exact isUnitary_*` per constructor; there the `exact`'s `isDefEq` does iota-reduce the matcher.
(Avoid `cases g <;> simp only [matcher] <;> first | exact … | …`: the brute-force `first` over
~14 alternatives × matrix `whnf` blew the 200000-heartbeat limit.)

## `Fin.cast_injective` takes the equality explicitly; `Nodup` → injective `get`

`Fin.cast_injective (h : n = m) : Function.Injective (Fin.cast h)` — the proof `h` is an
**explicit** argument, so write `Fin.cast_injective h.symm (proof_of_cast_eq)`, not
`Fin.cast_injective proof`. For a list, the lemma is `List.Nodup.injective_get`
(`l.Nodup → Function.Injective l.get`), not `…get_injective`; call it as
`List.Nodup.injective_get h` (dot notation `h.get_injective` mis-resolves through the
`Nodup = Pairwise (· ≠ ·)` unfolding to a nonexistent `List.Pairwise.get_injective`).
