# Architecture

Core design decisions and the rationale behind them.

## Core types

### `QMatrix n`

```lean
abbrev QMatrix (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
```

A square complex matrix of dimension 2^n. Gates are raw `QMatrix` values; unitarity is tracked separately as a predicate rather than bundled into the type. This avoids `.val` coercions throughout matrix proofs.

### `IsUnitary`

```lean
def IsUnitary {n} (U : QMatrix n) : Prop := U * Uᴴ = 1
```

One condition only. The other direction (`Uᴴ * U = 1`) is derived via `IsUnitary.conj_mul` using the Dedekind-finite monoid argument for square matrices. Keeping a single obligation minimizes proof burden at every call site.

### `Circuit`

```lean
inductive Circuit : ℕ → Type where
  | id   : Circuit n
  | gate : QMatrix n → Circuit n
  | seq  : Circuit n → Circuit n → Circuit n
  | par  : Circuit j → Circuit k → Circuit (j + k)
```

A structured syntax tree. `seq` is sequential composition (matrix-multiplication order: the rightmost factor acts first); `par` is parallel composition on disjoint wire sets. The qubit count is part of the type, so ill-typed tensor products are rejected at elaboration.

**Why not `List (QGate n)`?** A flat list cannot state general rewrite rules about circuit structure. The inductive type with `seq` and `par` makes the interchange law stateable and provable.

Notation: `c₁ * c₂` for `seq`, `c₁ ⊗ c₂` for `par`, `1` for `id`.

### `eval`

```lean
noncomputable def eval : Circuit n → QMatrix n
  | .id        => 1
  | .gate U    => U
  | .seq c₁ c₂ => eval c₁ * eval c₂   -- matrix product; c₂ (rightmost) applied first
  | .par c₁ c₂ => kron (eval c₁) (eval c₂)
```

The denotational semantics. Always returns `QMatrix n`; the `reindex` needed to bridge `Fin (2^j) × Fin (2^k)` to `Fin (2^(j+k))` is encapsulated inside `kron`.

### `Circuit.WF`

```lean
inductive Circuit.WF : Circuit n → Prop where
  | id   : WF .id
  | gate : IsUnitary U → WF (.gate U)
  | seq  : WF c₁ → WF c₂ → WF (.seq c₁ c₂)
  | par  : WF c₁ → WF c₂ → WF (.par c₁ c₂)
```

Unitarity of leaves is tracked as a separate predicate, not bundled into the `gate` constructor, for the same reason `IsUnitary` is kept separate from `QMatrix`. The bridge theorem `Circuit.eval_unitary : WF c → IsUnitary (eval c)` covers everything.

### `Circuit.Equiv`

```lean
def Circuit.Equiv (c₁ c₂ : Circuit n) : Prop := eval c₁ = eval c₂
notation:50 c₁ " ≈ " c₂ => Circuit.Equiv c₁ c₂
```

All circuit equalities reduce to matrix equality, closed by `ring`, `simp`, or basis-state reasoning.

---

## Tensor product (`kron`)

`Basic/Tensor.lean` defines `kron`, the reindexed Kronecker product:

```lean
noncomputable def kron (A : QMatrix j) (B : QMatrix k) : QMatrix (j + k) :=
  (Matrix.kronecker A B).reindex (tensorIndexEquiv j k) (tensorIndexEquiv j k)
```

`tensorIndexEquiv` is the only place `Matrix.reindex` appears. Everything above uses `kron` directly.

Key algebraic properties proved:
- `kron_mul` — mixed-product property: `kron (A*C) (B*D) = kron A B * kron C D`
- `kron_conjTranspose` — `(kron A B)ᴴ = kron Aᴴ Bᴴ`
- `kron_one_one` — `kron 1 1 = 1`
- `kron_assoc` — associativity up to `reindex`
- `IsUnitary.kron` — `IsUnitary A → IsUnitary B → IsUnitary (kron A B)`

---

## Gate embedding (`gateAt`)

`Gate/Embed.lean` provides a single embedding primitive:

```lean
noncomputable def gateAt (qs : Fin k ↪ Fin n) (U : QMatrix k) : QMatrix n
```

`U` acts on the `k` qubit positions selected by the embedding `qs`; identity on the rest. A direct matrix-entry formula avoids constructing permutation matrices. Key lemmas: `gateAt_mul`, `gateAt_one`, `gateAt_conjTranspose`, `gateAt_unitary`, `gateAt_comm_disjoint`.

Convenience wrappers: `hadamardAt`, `cnotAt`, `controlledAt`.

---

## Type-cast coherence for `par`

`par (par c₁ c₂) c₃ : Circuit ((j+k)+l)` and `par c₁ (par c₂ c₃) : Circuit (j+(k+l))` are different types because `(j+k)+l` and `j+(k+l)` are only propositionally equal. A named combinator handles this:

```lean
def Circuit.castN (h : m = n) (c : Circuit m) : Circuit n := h ▸ c
```

`Circuit.par_assoc` is stated as a `Circuit.Equiv` (eval-level equality) rather than a circuit-term equality — `castN` transports the type but not the term structure.

