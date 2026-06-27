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

### `QCircuit`

```lean
inductive QCircuit : ℕ → Type where
  | id   : QCircuit n
  | gate : QMatrix n → QCircuit n
  | seq  : QCircuit n → QCircuit n → QCircuit n
  | par  : QCircuit j → QCircuit k → QCircuit (j + k)
```

A structured syntax tree. `seq` is sequential composition (matrix-multiplication order: the rightmost factor acts first); `par` is parallel composition on disjoint wire sets. The qubit count is part of the type, so ill-typed tensor products are rejected at elaboration.

**Why not `List (QGate n)`?** A flat list cannot state general rewrite rules about circuit structure. The inductive type with `seq` and `par` makes the interchange law stateable and provable.

Notation: `c₁ * c₂` for `seq`, `c₁ ⊗ c₂` for `par`, `1` for `id`.

### `eval`

```lean
noncomputable def eval : QCircuit n → QMatrix n
  | .id        => 1
  | .gate U    => U
  | .seq c₁ c₂ => eval c₁ * eval c₂   -- matrix product; c₂ (rightmost) applied first
  | .par c₁ c₂ => kron (eval c₁) (eval c₂)
```

The denotational semantics. Always returns `QMatrix n`; the `reindex` needed to bridge `Fin (2^j) × Fin (2^k)` to `Fin (2^(j+k))` is encapsulated inside `kron`.

### `QCircuit.WF`

```lean
inductive QCircuit.WF : QCircuit n → Prop where
  | id   : WF .id
  | gate : IsUnitary U → WF (.gate U)
  | seq  : WF c₁ → WF c₂ → WF (.seq c₁ c₂)
  | par  : WF c₁ → WF c₂ → WF (.par c₁ c₂)
```

Unitarity of leaves is tracked as a separate predicate, not bundled into the `gate` constructor, for the same reason `IsUnitary` is kept separate from `QMatrix`. The bridge theorem `QCircuit.eval_unitary : WF c → IsUnitary (eval c)` covers everything.

### `QCircuit.Equiv`

```lean
def QCircuit.Equiv (c₁ c₂ : QCircuit n) : Prop := eval c₁ = eval c₂
notation:50 c₁ " ≈ " c₂ => QCircuit.Equiv c₁ c₂
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

## Positional embedding (`embed`)

`Basic/Embed.lean` lifts a `k`-qubit gate onto `k` chosen qubits of an `n`-qubit system:

```lean
def embed (qs : Fin k ↪ Fin n) (U : QMatrix k) : QMatrix n :=
  fun i j => if AgreeOff qs i j then U (selectIdx qs i) (selectIdx qs j) else 0
```

`par`/`⊗` can only place gates on *adjacent, in-order* wires; `embed` removes that
restriction — `qs` is an arbitrary injection, so the target qubits may be non-adjacent or
reordered (e.g. a CNOT straddling qubits `0` and `2`). This is the primitive that a future
positional circuit/`Program` layer needs.

**Why point-wise, not conjugation by a permutation.** A gate at arbitrary positions could
also be written `P · (U ⊗ I) · P⁻¹` for a qubit-permutation matrix `P`. That route forces an
`n - k` subtraction (the size of `I`), a cast for `k + (n - k) = n`, and the construction of
`P` from `qs`. The point-wise definition avoids all three: `selectIdx qs i` reads the selected
bits of an index directly, and `AgreeOff qs i j` ("the indices match on every unselected
qubit") plays the role of the identity factor. The algebra is then elementary:
`embed_one`, `embed_mul`, and `embed_conjTranspose` give `embed_unitary` exactly as
`IsUnitary.kron` is assembled for `kron`, and `embed_comm_disjoint` proves gates on disjoint
qubit sets commute.

An earlier `gateAt` (removed 2026-06-17) had the same point-wise shape but was never wired
into anything; `embed` is a fresh implementation with a cleaner `selectIdx`/`AgreeOff`
helper layer and a `mergeBits`-based fibre bijection for `embed_mul`.

---

## Type-cast coherence for `par`

`par (par c₁ c₂) c₃ : QCircuit ((j+k)+l)` and `par c₁ (par c₂ c₃) : QCircuit (j+(k+l))` are different types because `(j+k)+l` and `j+(k+l)` are only propositionally equal. A named combinator handles this:

```lean
def QCircuit.castN (h : m = n) (c : QCircuit m) : QCircuit n := h ▸ c
```

`QCircuit.par_assoc` is stated as a `QCircuit.Equiv` (eval-level equality) rather than a circuit-term equality — `castN` transports the type but not the term structure.

