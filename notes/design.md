# QLean Design Plan

This document records the architecture decisions for QLean and the reasoning behind them. Update it when a decision is revised, not when a decision is merely being explored.

---

## Goals and non-goals

**Goals:**
- A library for *equational reasoning* about quantum circuits — proving that two circuit descriptions denote the same unitary, or that a circuit implements a specific gate, by rewriting at the circuit-syntax level.
- Clean Lean 4 / Mathlib ergonomics: proofs should be short, `simp` should close routine goals, and the user should rarely need to think about `PiLp` or index arithmetic.
- A well-typed tensor product story: `Circuit.par c₁ c₂` should compose circuits on disjoint wire sets in a way that is both type-safe and easy to reason about.

**Non-goals:**
- A benchmark tool, LLM-training pipeline, or proof-automation contest (that's `autoquantum`).
- Measurement, mixed states, density matrices, or noise models (deferred to future work).
- Computational executability — all definitions can be `noncomputable`.

---

## Module layout

```
QLean/
  Basic/
    Matrix.lean       -- QMatrix, IsUnitary predicate, core simp lemmas
    PiLp.lean         -- Insulation layer: all PiLp/EuclideanSpace coercions (v1: placeholder only — no PiLp content until QState is introduced in v2)
  Gate/
    Standard.lean     -- H, X, Y, Z, S, T, Rz(θ), Rx(θ), Ry(θ), CNOT, CZ, SWAP, Toffoli
    Tensor.lean       -- kronQMatrix (reindexed Kronecker product) and its key lemmas
    Embed.lean        -- gateAt, onQubit, controlled-U construction
  Circuit/
    Type.lean         -- Circuit inductive type; castN
    Semantics.lean    -- eval : Circuit n → QMatrix n; Circuit.WF; coherence lemmas
    Rewrite.lean      -- Circuit.Equiv, equational rewrite rules
  Algorithm/          -- (future) Bell, GHZ, QFT, Grover
```

**Library root file:** `lake init` generates a `QLean.lean` at the repo root (alongside `lakefile.lean`) that re-exports submodules. Keep it in sync with the module layout above — add an `import` line for each new module. Without it, `import QLean` won't work; users would need module-specific imports like `import QLean.Circuit.Rewrite`.

**Note:** `Basic/Hilbert.lean` (QState, basis states, state-level action) is deferred to v2. The initial library targets matrix-level equational reasoning only; state-level reasoning can be layered on top without changing anything in the circuit layer.

**`Basic/PiLp.lean` in v1** is a one-line stub — it must exist as a Lean module (otherwise imports from higher-level files will fail) but contains no theorems:
```lean
import QLean.Basic.Matrix
-- v1 placeholder; EuclideanSpace / QState content deferred to v2
```

**Import dependency note:** The module layout table shows file structure, not import edges. The non-obvious required edge: `Circuit/Semantics.lean` must import `QLean.Gate.Tensor` (for `kronQMatrix` in `eval`'s `par` case). Without this import, `lake build` will fail with "unknown identifier 'kronQMatrix'" at the `eval` definition.

---

## Core type definitions

### QMatrix and IsUnitary

```lean
abbrev QMatrix (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

def IsUnitary {n} (U : QMatrix n) : Prop := U * Uᴴ = 1
```

One condition only: "rows are orthonormal" (`U * Uᴴ = 1`). The other direction is derived:

```lean
theorem IsUnitary.conj_mul {n} {U : QMatrix n} (h : IsUnitary U) : Uᴴ * U = 1
```

This follows from the finite-dimensional isometry argument (an isometry of a finite-dimensional inner product space is surjective). Using a single condition minimises the proof obligations at every call site.

A second derived lemma is needed for `Circuit.WF.eval_unitary` (the `seq` case):

```lean
theorem IsUnitary.mul {n} {U V : QMatrix n} (hu : IsUnitary U) (hv : IsUnitary V) :
    IsUnitary (U * V)
```

*Proof:* `(UV)(UV)ᴴ = U (V Vᴴ) Uᴴ = U 1 Uᴴ = U Uᴴ = 1`, using `Matrix.conjTranspose_mul` and `hu`/`hv`. Lives in `Basic/Matrix.lean`.

Gates are *not* bundled as `Matrix.unitaryGroup` by default. We work with raw `QMatrix` everywhere and carry `IsUnitary` hypotheses explicitly. This avoids constant coercions. A bundled subtype `QGate n := { U : QMatrix n // IsUnitary U }` is reserved for v2 contexts where the group structure is needed; it is not used anywhere in v1.

**Rationale:** The prototype used `Matrix.unitaryGroup` throughout and required `.val` coercions everywhere matrix entries or coordinates were needed. Unbundling keeps proofs cleaner.

### Circuit

```lean
inductive Circuit : ℕ → Type where
  | id   : Circuit n
  | gate : QMatrix n → Circuit n
  | seq  : Circuit n → Circuit n → Circuit n
  | par  : Circuit j → Circuit k → Circuit (j + k)
```

- `id` is the identity circuit (zero gates)
- `gate U` is a single unitary gate
- `seq c₁ c₂` applies `c₁` first, then `c₂` (left-to-right temporal order)
- `par c₁ c₂` runs `c₁` and `c₂` in parallel on disjoint wire sets

The `par` constructor carries the qubit count in its type, so ill-typed tensor products are rejected at elaboration time.

**Rationale:** A flat `List (QGate n)` (as in `autoquantum`) makes it impossible to state general rewrite rules about circuit structure (e.g., `par (seq c₁ c₂) (seq d₁ d₂) = seq (par c₁ d₁) (par c₂ d₂)` — the interchange law). An inductive type with `seq` and `par` constructors makes such laws stateable and provable.

### Denotational semantics

```lean
noncomputable def eval : Circuit n → QMatrix n
  | .id        => 1
  | .gate U    => U
  | .seq c₁ c₂ => eval c₂ * eval c₁       -- matrix product, c₁ applied first
  | .par c₁ c₂ => kronQMatrix (eval c₁) (eval c₂)
```

`eval` always returns a `QMatrix n` — the `Matrix.reindex` needed to bridge from `Fin (2^j) × Fin (2^k)` to `Fin (2^(j+k))` is encapsulated inside `kronQMatrix` (see Tensor product strategy below). Higher-level code never sees it.

**Key coherence theorems (to prove):**
- `eval_seq` : `eval (seq c₁ c₂) = eval c₂ * eval c₁`
- `eval_par` : `eval (par c₁ c₂) = kronQMatrix (eval c₁) (eval c₂)`
- `eval_id`  : `eval id = 1`
- Interchange law: `eval (par (seq a b) (seq c d)) = eval (seq (par a c) (par b d))`
- Unitarity preservation: `IsUnitary (eval c)` when all constituent gates are unitary

### Circuit.Equiv

```lean
def Circuit.Equiv (c₁ c₂ : Circuit n) : Prop := eval c₁ = eval c₂
```

This is the core equivalence relation. Everything reduces to matrix equality, closed by `ring`, `simp`, or `fin_cases i <;> fin_cases j` for small n.

`Circuit.Equiv` must be equipped with the standard equivalence-relation combinators so that `calc` blocks and chained rewrites work:

```lean
@[refl]  theorem Circuit.Equiv.refl  (c : Circuit n) : Circuit.Equiv c c
@[symm]  theorem Circuit.Equiv.symm  : Circuit.Equiv c₁ c₂ → Circuit.Equiv c₂ c₁
@[trans] theorem Circuit.Equiv.trans : Circuit.Equiv c₁ c₂ → Circuit.Equiv c₂ c₃ → Circuit.Equiv c₁ c₃

instance : Trans (@Circuit.Equiv n) (@Circuit.Equiv n) (@Circuit.Equiv n) :=
  ⟨Circuit.Equiv.trans⟩
```

All three lemmas are one-liners (`rfl`, `Eq.symm`, `Eq.trans`). The `Trans` instance is required for Lean 4's `calc` notation — `@[trans]` alone is insufficient. Both go at the top of `Circuit/Rewrite.lean` before any rewrite rules.

Two congruence lemmas are also required; without them `Circuit.Equiv` cannot be used to replace subterms inside a larger circuit:

```lean
theorem Circuit.Equiv.seq_congr {c₁ c₁' c₂ c₂' : Circuit n}
    (h₁ : Equiv c₁ c₁') (h₂ : Equiv c₂ c₂') : Equiv (seq c₁ c₂) (seq c₁' c₂')

theorem Circuit.Equiv.par_congr {c₁ c₁' : Circuit j} {c₂ c₂' : Circuit k}
    (h₁ : Equiv c₁ c₁') (h₂ : Equiv c₂ c₂') : Equiv (par c₁ c₂) (par c₁' c₂')
```

Both are one-liners: `simp [eval_seq, h₁, h₂]` and `simp [eval_par, h₁, h₂]` respectively. They go in `Circuit/Rewrite.lean` immediately after the `Trans` instance.

---

## Tensor product strategy

`Gate/Tensor.lean` defines `kronQMatrix`, the reindexed Kronecker product:

```lean
private noncomputable def tensorIndexEquiv (j k : ℕ) :
    Fin (2^j) × Fin (2^k) ≃ Fin (2^(j+k)) :=
  -- (a, b) ↦ a.val + b.val * 2^j  (A occupies the LOW j bits; consistent with LSB qubit convention)
  -- Note: plain finProdFinEquiv maps (a,b) ↦ a.val * 2^k + b.val (MSB-first), which would put A
  -- in the high bits — wrong for LSB. Equiv.prodComm swaps to get A in the low bits.
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [mul_comm, ← pow_add])))

noncomputable def kronQMatrix (A : QMatrix j) (B : QMatrix k) : QMatrix (j+k) :=
  (Matrix.kronecker A B).reindex (tensorIndexEquiv j k) (tensorIndexEquiv j k)
```

This is the **only** place `tensorIndexEquiv` and `Matrix.reindex` appear. Everything else uses `kronQMatrix` directly.

Key theorems in `Gate/Tensor.lean`:

```lean
theorem kronQMatrix_mul (A C : QMatrix j) (B D : QMatrix k) :
    kronQMatrix (A * C) (B * D) = kronQMatrix A B * kronQMatrix C D

theorem kronQMatrix_assoc (A : QMatrix j) (B : QMatrix k) (C : QMatrix l) :
    (kronQMatrix (kronQMatrix A B) C).reindex
        (finCongr (congr_arg (2^·) (Nat.add_assoc j k l)))
        (finCongr (congr_arg (2^·) (Nat.add_assoc j k l))) =
    kronQMatrix A (kronQMatrix B C)

theorem kronQMatrix_conjTranspose (A : QMatrix j) (B : QMatrix k) :
    (kronQMatrix A B)ᴴ = kronQMatrix Aᴴ Bᴴ

theorem kronQMatrix_one_one : kronQMatrix (1 : QMatrix j) (1 : QMatrix k) = 1
```

`kronQMatrix_mul` proof: `Matrix.kronecker_mul` gives the mixed-product property on the unindexed type; `Matrix.reindex_mul` lifts it to `QMatrix`. This one lemma implies the interchange law and unitarity preservation for `par`.

`kronQMatrix_assoc` proof: `Matrix.kronecker_assoc` gives associativity on the raw type; lifting through `reindex` requires a named coherence helper — call it `tensorIndexEquiv_assoc`:

```lean
private theorem tensorIndexEquiv_assoc (j k l : ℕ) :
    (tensorIndexEquiv (j+k) l).symm.trans
        ((tensorIndexEquiv j k).prodCongr (Equiv.refl _)) =
    (Equiv.prodAssoc _ _ _).trans
        ((Equiv.refl _).prodCongr (tensorIndexEquiv k l) |>.trans (tensorIndexEquiv j (k+l)).symm)
    -- (roughly: the two ways to build  Fin(2^j) × Fin(2^k) × Fin(2^l) ≃ Fin(2^(j+k+l))  agree)
```

The exact form depends on how `Matrix.reindex_trans` and `Matrix.reindex_mul` interact; write it as an `Equiv.ext` proof. **Do not use `omega` for the arithmetic here** — `omega` handles linear arithmetic but cannot derive `2^j * 2^k = 2^(j+k)`. Do not use `ring` alone either — `ring` in Lean 4 treats variable exponents as opaque atoms and cannot derive `2^(j+k) = 2^j * 2^k`. The correct sequence is: `rw [Nat.pow_add]` (or `rw [pow_add]`) first to substitute `2^(j+k) = 2^j * 2^k`, then `ring` closes the resulting polynomial goal. The key identity `a.val + (b.val + c.val * 2^k) * 2^j = a.val + b.val * 2^j + c.val * 2^j * 2^k` is then a straightforward ring goal over `ℕ`. **This is a required helper lemma for `kronQMatrix_assoc` — do not skip it.** It is the same category of proof risk as `Matrix.kronecker_assoc` itself. Needed by `par_assoc` at the eval level.

**Important:** The statement above is a sketch. Before committing to this form, work it out in a scratch file. Specifically, `kronQMatrix_assoc` leaves one side with a `.reindex` applied to the kronecker product, and `par_assoc` arrives via `eval_castN` which also introduces a `.reindex`. These two `reindex` calls need to compose; you may need a `Matrix.reindex_trans` (or `Matrix.reindex_reindex`) lemma to collapse them. If Mathlib does not provide one, prove it as a local helper in `Gate/Tensor.lean`:

```lean
private theorem reindex_trans {A : Matrix α β γ} (e₁ : α ≃ α') (e₂ : α' ≃ α'') ... :
    (A.reindex e₁ f₁).reindex e₂ f₂ = A.reindex (e₁.trans e₂) (f₁.trans f₂)
```

**Hard prerequisite: verify both `Matrix.kronecker_assoc` and `Matrix.reindex_mul` in a scratch file before writing any code in this file.** `Matrix.kronecker_assoc` may not exist in Mathlib under that name, or may already involve a reindexing between `(α × β) × γ` and `α × (β × γ)` index types that requires the full `tensorIndexEquiv_assoc` argument anyway. The direct `Matrix.ext` path — unpack `kronQMatrix` via `kronecker_apply` + `reindex`, apply `tensorIndexEquiv_assoc` to change the summation variable, close with `mul_assoc` over `ℂ` — does not depend on `Matrix.kronecker_assoc` at all and should be treated as the **expected** proof path, not the fallback. `Matrix.kronecker_assoc` is a shortcut if it exists with a compatible statement; check the scratch file first and prefer whichever is shorter. `Matrix.reindex_mul` is likely absent from Mathlib under that name — treat a local `Matrix.ext` proof as the expected path, not the fallback. Additionally, do not start `kronQMatrix_assoc` until `tensorIndexEquiv_assoc` type-checks in a scratch file; the `Equiv` composition in that proof is the highest-risk piece in the library and a wrong statement can look plausible while producing an incorrect result. **Lean 4 `×`-associativity pitfall**: `×` is right-associative in Lean 4, so `Fin (2^j) × Fin (2^k) × Fin (2^l)` means `Fin (2^j) × (Fin (2^k) × Fin (2^l))` — right-nested. The LHS of the `tensorIndexEquiv_assoc` sketch uses `.prodCongr` on `tensorIndexEquiv j k`, whose domain is `Fin (2^j) × Fin (2^k)` — left-nested. To compose these, `Equiv.prodAssoc` must rearrange the nesting before `.prodCongr` applies. The statement as sketched above may not type-check without this adjustment; verify the full type in a scratch file before writing any proof.

`kronQMatrix_conjTranspose` proof: `Matrix.star_kronecker` (or `Matrix.conjTranspose_kronecker`) gives `(A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ` on the raw type; `Matrix.reindex_conjTranspose` lifts it. Required for the `par` case of `WF.eval_unitary`.

`kronQMatrix_one_one` proof: `Matrix.one_kronecker_one` on the raw type; lift through `reindex` using `Matrix.reindex_one`. Required for the `par` case of `WF.eval_unitary`.

*Note:* `WF.eval_unitary` at the `par` case reduces `IsUnitary (kronQMatrix A B)` to `kronQMatrix (A * Aᴴ) (B * Bᴴ) = 1` via `kronQMatrix_mul` + `kronQMatrix_conjTranspose`, then `kronQMatrix_one_one` closes the goal.

---

## Qubit addressing

`Gate/Embed.lean` provides:

```lean
-- Apply a k-qubit gate to a specified k-tuple of distinct qubit positions in an n-qubit system
noncomputable def gateAt (qs : Fin k ↪ Fin n) (U : QMatrix k) : QMatrix n :=
  fun i j =>
    let f := finFunctionFinEquiv.symm i   -- decompose index into per-qubit bits
    let g := finFunctionFinEquiv.symm j
    U (finFunctionFinEquiv (f ∘ qs)) (finFunctionFinEquiv (g ∘ qs)) *
    if ∀ l : Fin n, (∀ m, qs m ≠ l) → f l = g l then 1 else 0
```

U acts on the k bits selected by `qs`; the remaining n-k bits must agree between row and column index (identity on the complement). This direct-entry formula avoids constructing an explicit permutation matrix; correctness proofs are point-wise calculations.

**Key lemmas to prove:**
- `gateAt_mul` : `gateAt qs (A * B) = gateAt qs A * gateAt qs B`  
  *Proof note: the hardest lemma in the library — expect it to take 3–4× longer than it looks. The RHS is `∑ l : Fin (2^n), (gateAt qs A i l) * (gateAt qs B l j)`. A term is non-zero only when `l` agrees with `i` on the complement of `qs` AND agrees with `j` on the complement of `qs`. If `i` and `j` disagree anywhere on the complement, all terms are zero and both sides vanish (the LHS gate entry also requires `i`/`j` agreement, so it is 0 too). When `i` and `j` agree on the complement, the surviving `l`s are exactly those that share the complement value of `i`/`j` but are free on the `k` bits indexed by `qs`. These form a set of size `2^k`, in bijection with `Fin (2^k)` via `l ↦ finFunctionFinEquiv (finFunctionFinEquiv.symm l ∘ qs)`. Rewrite the sum via `Finset.sum_nbij` (or `Finset.sum_equiv`) using this bijection; the summand collapses to `A (π i) m * B m (π j)` where `π i := finFunctionFinEquiv (finFunctionFinEquiv.symm i ∘ qs)` is the projection onto the `qs`-indexed bits. The resulting sum is exactly `(A * B) (π i) (π j)`, recovering the LHS.*

  **`mergeBits` helper (define before attempting this proof).** The inverse of `l ↦ π l` needed by `Finset.sum_nbij` is a "bit-merge" function: given complement bits from `i` and selected bits from some `m : Fin (2^k)`, reconstruct a full index `l : Fin (2^n)`. Define it before the proof:

  ```lean
  private noncomputable def mergeBits (qs : Fin k ↪ Fin n)
      (complement : Fin n → Fin 2) (selected : Fin k → Fin 2) : Fin (2^n) :=
    finFunctionFinEquiv (fun l =>
      if h : ∃ a, qs a = l then selected h.choose else complement l)
  ```

  The `h.choose` is well-defined because `qs` is injective (if `qs a = l` and `qs b = l` then `a = b`, so the choice is unique). Key properties to prove about `mergeBits` before using it in `sum_nbij`: (a) `finFunctionFinEquiv.symm (mergeBits qs c s) ∘ qs = s` (selected bits round-trip), (b) `∀ l, (∀ a, qs a ≠ l) → finFunctionFinEquiv.symm (mergeBits qs c s) l = c l` (complement bits round-trip), (c) `mergeBits qs (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm i ∘ qs) = i` (round-trip from a full index). Property (c) makes `mergeBits` the inverse of the sum-of-survivors bijection. All three follow by `Fin.ext` + case analysis on whether `l` is in `range qs`. **`open Classical` required:** The `if h : ∃ a, qs a = l` guard needs `Decidable (∃ a : Fin k, qs a = l)`; add `open Classical` at the top of `Gate/Embed.lean` (consistent with `noncomputable` throughout).*
- `gateAt_one` : `gateAt qs 1 = 1`  
  *Proof note: non-trivial despite the simple statement. Unfolding gives `1 (π i) (π j) * comp_if(i,j)`, and `1 (π i) (π j) = if π i = π j then 1 else 0`. The goal reduces to: `π i = π j ∧ complement_cond ↔ i = j`. The forward direction uses injectivity of `finFunctionFinEquiv` (selected bits match ↔ `π i = π j`) combined with the complement condition (remaining bits match), together implying `f_i = f_j` pointwise, hence `i = j` by `finFunctionFinEquiv.injective`. Prove this argument as a small sub-lemma before the main `Matrix.ext` proof.*
- `gateAt_conjTranspose` : `(gateAt qs U)ᴴ = gateAt qs Uᴴ`  
  *Proof:* `Matrix.ext`; `(gateAt qs U)ᴴ i j = conj ((gateAt qs U) j i)`. Unfolding the pointwise formula: `conj (U (π j) (π i) * b) = conj (U (π j) (π i)) * conj b` where `b ∈ {0, 1} ⊂ ℝ`, so `conj b = b`. Then `conj (U (π j) (π i)) = Uᴴ (π i) (π j)` by `Matrix.conjTranspose_apply`. The complement-agreement condition `∀ l ∉ range qs, f l = g l` is symmetric in `i` and `j`, so the `if` value is the same on both sides. Result: `gateAt qs Uᴴ i j`. The key fact that the `if`-guard value is real (hence invariant under `conj`) should be extracted as a one-line sub-lemma.*
- `gateAt_unitary` : `IsUnitary U → IsUnitary (gateAt qs U)`  
  *Proof: `gateAt_mul` + `gateAt_conjTranspose` reduce this to `gateAt qs (U * Uᴴ) = 1`, then `gateAt_one`.*
- `gateAt_comm_disjoint` : `Disjoint (Set.range qs₁) (Set.range qs₂) → gateAt qs₁ A * gateAt qs₂ B = gateAt qs₂ B * gateAt qs₁ A`  
  *Proof note: the sum collapses to a single term — this is **simpler** than `gateAt_mul`, not comparable. The key insight is that the two complement conditions together uniquely determine `l`:*
  - *Condition A (from `gateAt qs₁`): `l` agrees with `i` on complement(`qs₁`), which by disjointness includes all `range(qs₂)` — so `l`'s `qs₂`-bits are fixed to `i`'s.*
  - *Condition B (from `gateAt qs₂`): `l` agrees with `j` on complement(`qs₂`), which by disjointness includes all `range(qs₁)` — so `l`'s `qs₁`-bits are fixed to `j`'s.*
  - *Outer bits (not in `range(qs₁) ∪ range(qs₂)`): `l` must equal both `i` and `j`, so `i = j` at outer positions is required for any non-zero term.*

  *There is therefore at most ONE non-zero term in the sum. Use `Finset.sum_eq_single l₀` where `l₀` is the unique valid intermediate index, defined explicitly:*

  ```lean
  -- Let fi = finFunctionFinEquiv.symm i, fj = finFunctionFinEquiv.symm j
  private noncomputable def commDisjointMid
      (qs₁ : Fin j ↪ Fin n) (qs₂ : Fin k ↪ Fin n)
      (i₀ j₀ : Fin (2^n)) : Fin (2^n) :=
    let fi := finFunctionFinEquiv.symm i₀
    let fj := finFunctionFinEquiv.symm j₀
    finFunctionFinEquiv (fun l =>
      if ∃ a, qs₁ a = l then fj l   -- qs₁-bits from j₀
      else fi l)                      -- qs₂-bits and outer bits from i₀
  ```

  *Note on the simplified form:* The original sketch had three branches (`qs₁` / `qs₂` / outer), but the `qs₂` and outer cases both assign `fi l`. Since `qs₁` and `qs₂` are disjoint by hypothesis, the single `if/else` is equivalent. The uniqueness proof (property (b) above) only needs case analysis on whether `l ∈ range qs₁` or not; the `qs₂`-vs-outer distinction is irrelevant for `commDisjointMid`'s definition and only appears in the verification that both complement conditions are satisfied.*

  *Key properties to prove about `commDisjointMid` before using it in `sum_eq_single`:*
  - *(a) membership: `commDisjointMid qs₁ qs₂ i j ∈ Finset.univ` — trivial*
  - *(b) uniqueness: any other `l'` satisfying both complement conditions equals `commDisjointMid` — prove by `Fin.ext` + case analysis on whether each bit position is in `range qs₁`, `range qs₂`, or neither; disjointness ensures the cases are exhaustive and non-overlapping*
  - *(c) the single non-zero term evaluates to `A (π₁ i) (π₁ j) * B (π₂ i) (π₂ j)` for both product orderings, which are equal by `mul_comm ℂ`*

  *`open Classical` is required (same as `Gate/Embed.lean` generally). The proof is a `Matrix.ext` + `Finset.sum_eq_single` argument; the mechanization requires injectivity reasoning for `l₀`'s uniqueness, but no bijection. **`mergeBits` is not needed here.***

Convenience wrappers:
- `hadamardAt (i : Fin n) : QMatrix n`
- `cnotAt (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : QMatrix n`  
  *Convention: `ctrl` is the control qubit index (LSB position); `tgt` is the target qubit index.*
- `controlledAt (ctrl tgt : Fin n) (h : ctrl ≠ tgt) (U : QMatrix 1) : QMatrix n`  
  *Implementation: `gateAt (pairEmbed ctrl tgt h) (controlled U)` where `controlled U : QMatrix 2` is the 2-qubit controlled-U gate defined in `Gate/Standard.lean`:*
  ```lean
  -- ctrl = qubit 0 (low bit), tgt = qubit 1 (high bit); LSB convention
  -- Action: if ctrl=0, identity on tgt; if ctrl=1, apply U to tgt
  noncomputable def controlled (U : QMatrix 1) : QMatrix 2 :=
    !![1,      0, 0,      0;
       0, U 0 0, 0, U 0 1;
       0,      0, 1,      0;
       0, U 1 0, 0, U 1 1]
  ```
  *Derivation: index i = i₀ + 2·i₁ (i₀ = ctrl bit, i₁ = tgt bit). When i₀=0 (ctrl off): identity, so M_{r,c} = δ_{r,c}. When i₀=1 (ctrl on): apply U to tgt while keeping ctrl=1, so M_{r,c} = δ_{r₀,1} · U_{r₁, c₁}. The matrix above enumerates these four column cases for c=0,1,2,3.*

**Construction of `Fin k ↪ Fin n` from explicit indices.** Each wrapper is defined by constructing a small `Function.Embedding` and passing it to `gateAt`:

```lean
-- Single qubit at position i
private def singletonEmbed (i : Fin n) : Fin 1 ↪ Fin n :=
  ⟨Fin.cases i Fin.elim0, by intro a b _; fin_cases a <;> fin_cases b <;> simp⟩

-- Two qubits at positions ctrl, tgt (must be distinct)
private def pairEmbed (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : Fin 2 ↪ Fin n :=
  ⟨![ctrl, tgt], by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]⟩

def hadamardAt (i : Fin n) : QMatrix n := gateAt (singletonEmbed i) H
def cnotAt (ctrl tgt : Fin n) (h : ctrl ≠ tgt) : QMatrix n := gateAt (pairEmbed ctrl tgt h) CNOT
```

The `![]` notation constructs a `Fin k → Fin n` via `Matrix.vecCons`; injectivity is a `fin_cases` argument using `h`.

**Bridge between `gateAt` and `kronQMatrix` (v2):**

```lean
-- embedFirst j k : Fin j ↪ Fin (j+k)  maps  i ↦ i.castLE (Nat.le_add_right j k)
-- embedLast  j k : Fin k ↪ Fin (j+k)  maps  i ↦ ⟨j + i.val, by omega⟩
theorem kronQMatrix_eq_gateAt_mul (A : QMatrix j) (B : QMatrix k) :
    kronQMatrix A B = gateAt (embedFirst j k) A * gateAt (embedLast j k) B
```

This lemma bridges the `par`-based and `gateAt`-based representations (e.g., expressing a gate embedded inside one arm of a `par`). **Deferred to v2**: no v1 theorem depends on it, and the proof requires a non-trivial index-arithmetic argument relating `tensorIndexEquiv` to the `finFunctionFinEquiv`-based projection used by `gateAt`.

---

## What we deliberately differ from `autoquantum`

| `autoquantum` | QLean |
|---|---|
| `Circuit n = List (QGate n)` | `Circuit n` inductive with `seq`/`par` |
| `QGate n = Matrix.unitaryGroup …` | `QMatrix n = Matrix …`; `IsUnitary` separate predicate |
| Tensor product hand-rolled via `tensorIndexEquiv` | `Matrix.kronecker` as the primitive; one reindexing lemma |
| `PiLp` coercions scattered across proofs | All coercions insulated in `Basic/PiLp.lean` |
| Flat gate embedding (`onQubit`, `tensorWithId`, …) | Single `gateAt` with direct matrix-entry formula |
| Equational reasoning only at matrix level | Circuit-level rewrite rules via `Circuit.Equiv` |

---

## Toolchain

- **Lean:** latest stable (to be pinned once initialized)
- **Mathlib:** latest (to be pinned in `lakefile.lean` once initialized)
- `noncomputable` is expected and acceptable throughout

---

## Circuit well-formedness

Unitarity of a circuit's leaves is tracked by a separate inductive predicate, not bundled into the `Circuit` type:

```lean
inductive Circuit.WF : Circuit n → Prop where
  | id   : WF .id
  | gate : IsUnitary U → WF (.gate U)
  | seq  : WF c₁ → WF c₂ → WF (.seq c₁ c₂)
  | par  : WF c₁ → WF c₂ → WF (.par c₁ c₂)
```

One bridging theorem covers everything: `Circuit.WF.eval_unitary : WF c → IsUnitary (eval c)`.

**Module placement:** `Circuit.WF` lives in `Circuit/Semantics.lean`. It cannot go in `Circuit/Type.lean` because `Circuit/Type.lean` already imports `Basic/Matrix.lean` (for `QMatrix`), making a circular-free placement possible there, but `WF` depends on `IsUnitary` which also requires `Basic/Matrix.lean`. Since `Circuit/Semantics.lean` imports both `Circuit/Type.lean` and `Basic/Matrix.lean`, that is the natural home.

**Rationale:** Bundling unitarity into the `gate` constructor (i.e., `gate : QGate n → Circuit n`) would re-introduce `.val` coercions in `eval` — exactly the cost already paid to unbundle `IsUnitary` from `QMatrix`. A separate predicate keeps `Circuit` as clean syntax for rewrite rules, and structural induction on `WF` mirrors `Circuit` exactly.

---

## Qubit ordering convention

**Decision: LSB-first.** Qubit 0 is the least significant bit. A 2-qubit state |q₀q₁⟩ maps to index `q₀ + q₁ * 2`.

**Rationale:** Mathlib's `finFunctionFinEquiv : (Fin n → Fin 2) ≃ Fin (2^n)` is LSB-first (`f ↦ ∑ i, f(i) * 2^i`). The `gateAt` embedding uses `finFunctionFinEquiv.symm : Fin (2^n) → (Fin n → Fin 2)` to decompose an index into per-qubit bits; qubit `l` is `(finFunctionFinEquiv.symm i) l`. Using MSB-first would require a custom equivalence and all the proofs that come with it.

**Ket notation convention in comments:** Write kets as |q_{n-1}…q₁q₀⟩ — MSB-first string, but LSB-first index. So for 2 qubits: |00⟩=index 0, |01⟩=index 1 (q₀=1), |10⟩=index 2 (q₁=1), |11⟩=index 3. *This is the opposite of the index ordering; it matches standard textbook ket notation while using our internal LSB index.*

**Consequence for gate matrices:** Standard textbook gate matrices (e.g., CNOT) are written with MSB as the control. Our LSB-first index reorders rows and columns. Each gate in `Gate/Standard.lean` should carry a comment noting the qubit roles. Example: `cnotAt ctrl=0 tgt=1` (ctrl is the LOW qubit, i.e., q₀; tgt is q₁) has the swap block in rows/columns 1 and 3 (|01⟩ and |11⟩ in MSB-first notation, i.e., indices q₀=1 and q₀=1,q₁=1).

---

## Type-cast coherence for `par`

`par (par c₁ c₂) c₃ : Circuit ((j+k)+l)` and `par c₁ (par c₂ c₃) : Circuit (j+(k+l))` are different types because `(j+k)+l` and `j+(k+l)` are only propositionally equal. A named cast combinator handles this:

```lean
def Circuit.castN (h : m = n) (c : Circuit m) : Circuit n := h ▸ c
```

Associativity of `par` is stated as a `Circuit.Equiv` (i.e., eval-level equality):

```lean
theorem par_assoc (c₁ : Circuit j) (c₂ : Circuit k) (c₃ : Circuit l) :
    Circuit.Equiv
      (Circuit.castN (Nat.add_assoc j k l) (par (par c₁ c₂) c₃))
      (par c₁ (par c₂ c₃))
```

**Why not a circuit-term equality?** `castN h c := h ▸ c` changes the type annotation but not the term structure. For non-trivial `h` (i.e., when `Nat.add_assoc j k l` is not `rfl`, which is the case for variable `j k l`), `h ▸ par (par c₁ c₂) c₃` and `par c₁ (par c₂ c₃)` are structurally different inductive terms. No structural induction on `Circuit` can make them propositionally equal — the two terms live in `Circuit (j+(k+l))` via different construction paths. The eval-level statement is both correct and sufficient: it says two circuits compute the same unitary, which is what users need.

`par_assoc` unfolds to `eval (castN h ...) = eval (par c₁ (par c₂ c₃))` and is proved by `eval_castN` + `kronQMatrix_assoc`. The "double reindex" concern resolves cleanly: `eval_castN` introduces a `.reindex e₁` where `e₁ = finCongr (congr_arg (2^·) (Nat.add_assoc j k l))`, and `kronQMatrix_assoc` introduces a `.reindex e₂` with the same expression. Since `e₁` and `e₂` are definitionally equal, there is no extra composition step — `kronQMatrix_assoc` closes the goal directly after `eval_castN` is applied.

A simp lemma relates `castN` to matrix reindexing at the `eval` level:

```lean
@[simp] theorem eval_castN (h : m = n) (c : Circuit m) :
    eval (castN h c) = (eval c).reindex
        (finCongr (congr_arg (2^·) h)) (finCongr (congr_arg (2^·) h))
```

*Note: `finCongr h : Fin m ≃ Fin n` is the wrong type for `reindex`; `eval c : QMatrix m` needs `Fin (2^m) ≃ Fin (2^n)`. The correct argument is `finCongr (congr_arg (2^·) h) : Fin (2^m) ≃ Fin (2^n)`.*

**Proof of `eval_castN`:** `h : m = n` is a `ℕ`-valued equality (not a type-level equality), so there is no universe-motive problem. Use `cases h` to substitute `n := m` throughout the goal; the LHS becomes `eval (castN rfl c) = eval c` and the RHS has `Matrix.reindex (finCongr (congr_arg (2^·) rfl)) ... (eval c)` which reduces to `eval c` since `finCongr rfl = Equiv.refl _`. Proof: `cases h; simp [castN, Matrix.reindex_refl]` (or whichever `reindex`-identity lemma Mathlib provides). **Do not use `subst h`** — `subst` requires one side to be a local variable, which fails when `h : (j+k)+l = j+(k+l)` for free `j k l`.

`castN` lives in `Circuit/Type.lean`.

**Note on commutativity:** `castN` is *not* used for commutativity of `par`. `par c₁ c₂` and `par c₂ c₁` are structurally different circuit terms and are not propositionally equal in general. At the `eval` level, `kronQMatrix A B` and `kronQMatrix B A` differ by a non-trivial qubit-permutation (the perfect-shuffle), not a simple reindexing. Commutativity of `par` is deferred to future work.

**Rationale:** `HEq`-based casting is dead weight — `simp` and `rw` don't work with it. A named `castN` with a single `eval_castN` simp lemma keeps both levels clean. `par_assoc` is correctly stated as a `Circuit.Equiv` (eval-level equality) rather than a circuit-term equality, because `castN` transports the type but not the term structure — `h ▸ (par (par c₁ c₂) c₃)` and `par c₁ (par c₂ c₃)` are provably equal only at the `eval` level via `kronQMatrix_assoc`. Commutativity of `par` is deferred to future work for the same reason (and is harder: it requires a non-trivial qubit-permutation at the matrix level).

**`wf_castN` deferred to v2.** No v1 theorem needs `WF (castN h c) ↔ WF c` directly — `par_assoc` is purely an eval-level statement, and `WF.eval_unitary` is stated for concrete circuits, not cast ones. However, any user who applies `par_assoc` inside a larger WF circuit will immediately want this lemma. Add it in v2 as a one-liner (`cases h; simp [castN]`) alongside the other `wf_*` simp lemmas.

---

## `@[simp]` set design

The goal "simp closes routine goals" requires deliberate `@[simp]` attribution, not ad-hoc marking.

**Mark `@[simp]`:**
- `eval_id`, `eval_gate`, `eval_seq`, `eval_par`, `eval_castN` — the unfolding rules for `eval`; simp needs all five to reduce circuit expressions to matrix expressions. `eval_gate : eval (.gate U) = U` is definitionally `rfl` but must be explicitly attributed so `simp` unfolds `.gate` nodes.
- `gateAt_one` — `gateAt qs 1 = 1` is a canonical simplification at gate-embedding boundaries
- `wf_id`, `wf_gate`, `wf_seq`, `wf_par` — **iff-style lemmas** (not the constructors themselves) so `simp` can fully decompose well-formedness goals automatically:
  ```lean
  @[simp] theorem wf_id   : WF (.id : Circuit n) := WF.id
  @[simp] theorem wf_gate : WF (.gate U) ↔ IsUnitary U
  @[simp] theorem wf_seq  : WF (.seq c₁ c₂) ↔ WF c₁ ∧ WF c₂
  @[simp] theorem wf_par  : WF (.par c₁ c₂) ↔ WF c₁ ∧ WF c₂
  ```
  Do **not** tag the `WF` constructors themselves — constructors are not equations and `simp` cannot use them as rewrite rules. Including `wf_gate` (unlike the `wf_seq`/`wf_par` cases) does not risk a simp loop: it rewrites `WF (.gate U)` to `IsUnitary U`, which is strictly simpler and has no matching rewrite rule that would cycle back. Without it, `simp [wf_seq, wf_par]` would reduce a circuit's WF to a conjunction of `WF (.gate _)` goals that must each be closed manually; with it, simp reduces all the way to `IsUnitary` obligations in one shot.

**Do NOT mark `@[simp]`:**
- `kronQMatrix_mul` — rewrites `kronQMatrix (A*C) (B*D)` to a product; looping against matrix ring lemmas
- `gateAt_mul` — same risk; use as a targeted `rw` not a simp lemma
- `IsUnitary.*` lemmas — these are side conditions for explicit discharge, not simplification rules

**Intended proof idiom for circuit equivalences:**
```lean
-- Prove Circuit.Equiv c₁ c₂ (i.e., eval c₁ = eval c₂)
simp only [eval_seq, eval_par, eval_id, eval_gate, kronQMatrix_mul]
ring   -- or: norm_num for concrete gate entries
```
`simp` reduces both sides to a matrix-algebraic expression; `ring` (or `norm_num` when `Real.sqrt` entries are present) closes the goal.

---

## Multi-qubit gate matrices in LSB convention

`Gate/Standard.lean` defines explicit `QMatrix` values. The LSB-first index means row/column `i` corresponds to the bit pattern `finFunctionFinEquiv.symm i`, with qubit 0 in the least significant position. The standard textbook matrices (MSB-first) must be reordered. Concrete entries for the v1 gates:

**CNOT** — control = qubit 0 (low bit), target = qubit 1 (high bit).

| index | |q₁q₀⟩ | CNOT maps to |
|-------|--------|--------------|
| 0     | \|00⟩  | \|00⟩ = 0   |
| 1     | \|01⟩  | \|11⟩ = 3   |
| 2     | \|10⟩  | \|10⟩ = 2   |
| 3     | \|11⟩  | \|01⟩ = 1   |

Matrix (rows = output index, columns = input index, permutation matrix with 1s at the mapped positions):

```
CNOT = !![1, 0, 0, 0;
          0, 0, 0, 1;
          0, 0, 1, 0;
          0, 1, 0, 0]
```

This differs from the standard textbook `!![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]` (which uses control = high bit). Each gate definition in `Standard.lean` should carry a `-- ctrl = qubit 0, tgt = qubit 1` comment and a reference to this table.

**CZ** — symmetric in the two qubits; only `|11⟩` (index 3) gets a phase flip.

```
CZ = !![1, 0, 0,  0;
        0, 1, 0,  0;
        0, 0, 1,  0;
        0, 0, 0, -1]
```

This is the same as the textbook matrix (index 3 = `|11⟩` in both conventions).

**SWAP** — exchanges qubit 0 and qubit 1; swaps indices 1 (`|01⟩`) and 2 (`|10⟩`).

```
SWAP = !![1, 0, 0, 0;
          0, 0, 1, 0;
          0, 1, 0, 0;
          0, 0, 0, 1]
```

Same as the textbook matrix (SWAP is symmetric under qubit relabeling).

**Verification strategy:** Verify gate matrix entries by inspection (2×2 and 4×4 matrices are small enough to check by hand). Do NOT use `#eval` or `native_decide` — gate definitions are `noncomputable` (entries involve `ℂ`) and neither tactic can evaluate them. The `IsUnitary` proofs for CNOT/CZ/SWAP all close by `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]`.

---

## v1 completion criterion

The library is v1-complete when the following are proved:

**Project setup (before writing any theorems):**
- After `lake init`, update the generated `QLean.lean` root re-export file to import all six leaves: `QLean.Basic.Matrix`, `QLean.Basic.PiLp`, `QLean.Gate.Standard`, `QLean.Gate.Tensor`, `QLean.Gate.Embed`, `QLean.Circuit.Semantics`, `QLean.Circuit.Rewrite`. Without this, `import QLean` will not expose the full library.
- Initialize the project: run `lake init QLean math` from within the repo root (`~/research/QLean`) — this generates `lakefile.lean`, `lean-toolchain`, and a Mathlib-linked skeleton in-place. Do **not** use `lake new QLean math` (that command creates a *new* subdirectory and would conflict with the existing git repo). The `lean-toolchain` file must match the Mathlib commit pinned in `lakefile.lean`.
- `lake exe cache get` fetches prebuilt Mathlib oleans; `lake build` must succeed before any Lean files are written.
- Scratch file confirms:
  - `#check Matrix.kronecker_assoc` (existence and exact name)
  - `#check @finFunctionFinEquiv` (exact name, argument order, and that it is LSB-first for `(Fin n → Fin 2) ≃ Fin (2^n)`)
  - `#check Matrix.mul_eq_one_comm` (for `IsUnitary.conj_mul`)
  - `#check Matrix.one_kronecker_one` (for `kronQMatrix_one_one`; may be `Matrix.one_kronecker_one` or a different name)
  - `#check @Matrix.reindex_trans` (exists in Mathlib or must be proved locally)
  - `#check @Matrix.reindex_refl` (needed for `eval_castN` proof: `Matrix.reindex (Equiv.refl _) (Equiv.refl _) A = A` — may be named `Matrix.reindex_refl`, `Matrix.reindex_equiv_refl`, or derivable via `simp [Matrix.reindex, Equiv.refl]`)
  - `#check @Matrix.reindex_mul` (for `kronQMatrix_mul`; lifts `Matrix.kronecker_mul` through `reindex` — must exist or be proved locally)
  - `#check @Matrix.reindex_conjTranspose` (for `kronQMatrix_conjTranspose`; must exist or be proved locally)
  - `#check @Matrix.reindex_one` (for `kronQMatrix_one_one`; must exist or be proved locally)
  - `#check @Matrix.kronecker_mul` (the mixed-product property `(A ⊗ B) * (C ⊗ D) = (A*C) ⊗ (B*D)`; the foundation of `kronQMatrix_mul` — `Matrix.reindex_mul` only lifts it. Verify it exists under this exact name; it may be `Matrix.mul_kronecker_mul` or similar)
  - `#check @Matrix.star_kronecker` (for `kronQMatrix_conjTranspose`; also try `Matrix.conjTranspose_kronecker`. If absent under both names, search for `kronecker` in `Mathlib.LinearAlgebra.Matrix.Kronecker` and record the actual name in `notes/lean-api.md` before writing any code)
  - `#check @Finset.sum_nbij` (for `gateAt_mul`; its required arguments have changed across Mathlib versions — confirm the current signature before writing the bijection argument)
  - `#check @Finset.sum_eq_single` (for `gateAt_comm_disjoint`; used to collapse the product sum to a single non-zero term — confirm the current signature and required decidability instances)
  - `#check @Finset.sum_equiv` (for `kronQMatrix_mul` if `Matrix.reindex_mul` is absent — the proof needs a sum-variable change from `l : Fin (2^j) × Fin (2^k)` to `l' : Fin (2^(j+k))` via `tensorIndexEquiv`; also try `Finset.sum_bijOn`. Confirm the current signature before writing the variable-change argument)
  - `#check Matrix.cons_val_zero` and `#check Matrix.cons_val_one` (used in the `pairEmbed` injectivity proof; these names have changed across Mathlib versions — if absent, search for the simp lemmas that reduce `![a, b] 0` and `![a, b] 1`)
  - Confirm `finCongr`: run `#check @finCongr` to verify it exists with type `m = n → Fin m ≃ Fin n` in your Mathlib version. The design uses `finCongr` throughout (including inside `tensorIndexEquiv`). If `finCongr` is absent, find its current name (possibly `Fin.castEquiv`) and update all usages in the design consistently before writing any code.
  - `#check @finCongr_rfl` (or confirm `finCongr rfl = Equiv.refl _` by `rfl`): needed for the `eval_castN` proof — after `cases h`, the RHS has `finCongr (congr_arg (2^·) rfl)` which must reduce to `Equiv.refl _` so that `Matrix.reindex_refl` applies. If no `finCongr_rfl` lemma exists, confirm this reduces by `simp [finCongr, Equiv.refl]` or `rfl`.
- If any of these are missing or differently named, update `notes/lean-api.md` and revise the affected proof paths before writing code.

**`Basic/Matrix.lean`:** `IsUnitary.conj_mul`, `IsUnitary.mul`

**`Gate/Standard.lean`:** `H`, `X`, `Y`, `Z`, `CNOT` defined and shown unitary. The `sqrt2_sq_cast` helper (`(Real.sqrt 2 : ℂ)^2 = 2`) must be proved first — it is a prerequisite for `H`'s unitarity proof. Also define `controlled (U : QMatrix 1) : QMatrix 2` here and prove `IsUnitary (controlled U)` (proof: `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]`, discharging the U-block entries with `hu : U * Uᴴ = 1`; this lemma is required by `controlledAt` in `Gate/Embed.lean`).

  *Tactic note for `IsUnitary (controlled U)`:* `simp [Matrix.mul_apply]` alone cannot use `hu : IsUnitary U` — it only knows `hu : U * Uᴴ = 1` as a matrix equation. To discharge individual-entry goals, extract entries explicitly:
  ```lean
  have hu' : ∀ a b, (U * Uᴴ) a b = (1 : QMatrix 1) a b := congr_fun₂ hu
  simp [Matrix.mul_apply] at hu' ⊢
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.mul_apply, Matrix.conjTranspose_apply]
  ```
  Alternatively, `have h00 := hu' 0 0; have h01 := hu' 0 1` etc. to name the four scalar conditions before the `fin_cases` discharge. `S`, `T`, `Rz`, `Rx`, `Ry`, `CZ`, `SWAP`, `Toffoli` are *defined* in this file but their unitarity proofs are deferred to v2: parametric gates (`T`, `Rz`, `Rx`, `Ry`) require trigonometric/exponential identities not addressed in this design; permutation gates (`CZ`, `SWAP`, `Toffoli`) are provable by `fin_cases` but are not on the critical path for v1.

**`Gate/Tensor.lean`:** `reindex_trans` local helper (if not in Mathlib — check `#check @Matrix.reindex_trans` first), `tensorIndexEquiv_assoc`, `kronQMatrix_mul`, `kronQMatrix_assoc`, `kronQMatrix_conjTranspose`, `kronQMatrix_one_one`

**`Gate/Embed.lean`:** `gateAt_mul`, `gateAt_one`, `gateAt_conjTranspose`, `gateAt_unitary`, `gateAt_comm_disjoint`; also `IsUnitary (hadamardAt i)`, `IsUnitary (cnotAt ctrl tgt h)`, and `IsUnitary (controlledAt ctrl tgt h U)` (the first two fall out of `gateAt_unitary` applied to `H` and `CNOT`; the last requires `gateAt_unitary` applied to `controlled U`, so `IsUnitary (controlled U)` from `Gate/Standard.lean` must be imported first)

**`Circuit/Semantics.lean`:** `eval_id`, `eval_gate`, `eval_seq`, `eval_par`, `eval_castN`, interchange law, `Circuit.WF.eval_unitary`; also `wf_id`, `wf_gate`, `wf_seq`, `wf_par` (the iff-style simp lemmas for `WF`)

**`Circuit/Rewrite.lean`:** `Circuit.Equiv.refl`, `.symm`, `.trans` (with `@[refl]`/`@[symm]`/`@[trans]`); `Trans` instance; `seq_congr`, `par_congr`; `seq_id_left`, `seq_id_right`, `seq_assoc`, `par_assoc` (as `Circuit.Equiv`, proved via `eval_castN` + `kronQMatrix_assoc`)

Everything else is v2: algorithms (Bell, GHZ, QFT, Grover), state-level reasoning (`Basic/Hilbert.lean`), `par_comm`, `kronQMatrix_eq_gateAt_mul` (the bridge between `par`- and `gateAt`-based representations), `QGate` subtype usage.
