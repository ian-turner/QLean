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
  | id    : QCircuit n
  | gate  : QMatrix n → QCircuit n
  | seq   : QCircuit n → QCircuit n → QCircuit n
  | par   : QCircuit j → QCircuit k → QCircuit (j + k)
  | embed : (Fin k ↪ Fin n) → QCircuit k → QCircuit n
```

A structured syntax tree. `seq` is sequential composition (matrix-multiplication order: the rightmost factor acts first); `par` is parallel composition on disjoint wire sets; `embed qs c` places the `k`-qubit sub-circuit `c` at the qubits selected by `qs : Fin k ↪ Fin n` (an arbitrary injection) — the addressing primitive for non-adjacent / reordered placement that `par` cannot express. The qubit count is part of the type, so ill-typed tensor products are rejected at elaboration. See *Embedding as a circuit constructor* below for why `embed` is a constructor rather than `gate ∘ embedₘ`.

**Why not `List (QGate n)`?** A flat list cannot state general rewrite rules about circuit structure. The inductive type with `seq` and `par` makes the interchange law stateable and provable.

Notation: `c₁ * c₂` for `seq`, `c₁ ⊗ c₂` for `par`, `1` for `id`; `embed` has no infix (write `QCircuit.embed qs c`).

### `eval`

```lean
noncomputable def eval : QCircuit n → QMatrix n
  | .id         => 1
  | .gate U     => U
  | .seq c₁ c₂  => eval c₁ * eval c₂   -- matrix product; c₂ (rightmost) applied first
  | .par c₁ c₂  => kron (eval c₁) (eval c₂)
  | .embed qs c => embed qs (eval c)   -- the matrix `embed` of Basic/Embed.lean, on the denotation
```

The denotational semantics. Always returns `QMatrix n`; the `reindex` needed to bridge `Fin (2^j) × Fin (2^k)` to `Fin (2^(j+k))` is encapsulated inside `kron`, and the `embed` case delegates to the matrix `embed` of `Basic/Embed.lean` — so the constructor adds no new semantics, only first-class syntax.

### `QCircuit.WF`

```lean
def QCircuit.WF : QCircuit n → Prop
  | .id         => True
  | .gate U     => IsUnitary U
  | .seq c₁ c₂  => WF c₁ ∧ WF c₂
  | .par c₁ c₂  => WF c₁ ∧ WF c₂
  | .embed _ c  => WF c
```

A `def` by structural recursion (not an `inductive`), which sidesteps dependent-elimination friction on the heterogeneous `par`/`embed` arity indices. Unitarity of leaves is tracked as a separate predicate, not bundled into the `gate` constructor, for the same reason `IsUnitary` is kept separate from `QMatrix`. The bridge theorem `QCircuit.eval_unitary : WF c → IsUnitary (eval c)` covers everything (the `embed` case is just `embed_unitary qs (ih h)`).

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
qubit sets commute. Two further laws support the circuit-level constructor (below):
`embed_embed` (`embed qs (embed qs2 U) = embed (qs2.trans qs) U`, composing addressing maps) and
`embed_kron_factor` (`embed qs (kron A B) = embed (lowEmb.trans qs) A * embed (highEmb.trans qs) B`,
splitting a tensor across the low/high coordinate blocks `lowEmb`/`highEmb : Fin _ ↪ Fin (j+k)`).

An earlier `gateAt` (removed 2026-06-17) had the same point-wise shape but was never wired
into anything; `embed` is a fresh implementation with a cleaner `selectIdx`/`AgreeOff`
helper layer and a `mergeBits`-based fibre bijection for `embed_mul`.

---

## Embedding as a circuit constructor

`embed` is also a **constructor of `QCircuit`** (`embed : (Fin k ↪ Fin n) → QCircuit k → QCircuit n`),
not merely the matrix function wrapped in `gate`. Its semantics delegates to the matrix `embed`:
`eval (embed qs c) = embed qs (eval c)`, and `WF (embed qs c) = WF c`.

**Why first-class.** The matrix `embed` is already maximally expressive — it places any gate at any
injective set of qubits — so the constructor adds *no expressiveness*. What it adds is that
embeddings are **visible in the syntax tree**: a circuit-to-circuit transformation (topology
routing, locality-aware optimization, resource counting) can pattern-match an `embed` and read its
addressing `qs`, whereas `gate (embedₘ qs U)` flattens the placement into an opaque matrix. It also
makes well-formedness/unitarity structural — the `embed` case of `eval_unitary` is just
`embed_unitary qs (ih h)`.

**Why `par` is kept, not derived.** A `kron` is a special case of two embeddings on disjoint
contiguous blocks (`embed_kron_factor`), so `par` *could* be derived from `embed`. We keep `par` as
its own constructor: removing it would break every `⊗`, the
`par_action_tensor`/`par_assoc`/`interchange_law` lemmas, and re-open the `j + k` index pain
doubled. Instead the bridge `QCircuit.par_as_embed` (`c₁ ⊗ c₂ ≈ embed (lowEmb) c₁ * embed (highEmb) c₂`,
with `embed_par_split` its already-embedded form) lets a pass normalize `par` into `embed` when
a uniform view is wanted.

**The circuit-level algebra** lives in `Circuit/Embed.lean` as `≈`-lemmas, each reducing to the
matrix algebra above: `embed_gate` (bridge to `gate (embedₘ qs U)`), `embed_id`, `embed_seq`
(distributes over `*`), `embed_comp` (composes addressing maps via `qs2.trans qs`),
`embed_par_split`, `par_as_embed`, and `embed_comm_disjoint`. The action lemmas `embed_diag_action` /
`embed_single_action` describe how an embedded gate acts on a basis ket — the entry points the
per-layer correctness proofs (e.g. the QFT) use.

---

## Type-cast coherence for `par`

`par (par c₁ c₂) c₃ : QCircuit ((j+k)+l)` and `par c₁ (par c₂ c₃) : QCircuit (j+(k+l))` are different types because `(j+k)+l` and `j+(k+l)` are only propositionally equal. A named combinator handles this:

```lean
def QCircuit.castN (h : m = n) (c : QCircuit m) : QCircuit n := h ▸ c
```

`QCircuit.par_assoc` is stated as a `QCircuit.Equiv` (eval-level equality) rather than a circuit-term equality — `castN` transports the type but not the term structure.


---

## The `Program` IR and OpenQASM compilation

`QCircuit` is the *semantic* IR: maximally expressive (it carries raw `ℂ`-matrices), and its
`eval` is noncomputable and unprintable. `Program` (`QLean/Program/`) is the *syntactic,
serializable* IR layered on top — the frontend a compiler and (later) a simulator need.

```lean
inductive Program : ℕ → Type where
  | id   : Program n
  | prim : (g : Prim) → (Fin g.arity ↪ Fin n) → Program n
  | seq  : Program n → Program n → Program n
```

A `Program` stores **only** gate *names* (`Prim`), symbolic *angles* (`Angle := ℚ` multiples
of `π`), and qubit *indices* — never a matrix. So it is computable and serializes directly to
OpenQASM (`Program.toQASM`, e.g. `rz(pi/4) q[2];`, `cp(pi/4) q[0], q[1];`).

**Why a separate IR, given `embed` already places gates anywhere.** Since `embed` became a
`QCircuit` constructor, `Program` is *not* needed for expressiveness — `QCircuit` can already
express any placement. `Program`'s job is the one thing `QCircuit` cannot do: name gates
symbolically so they can be **printed** (and angle-formatted as `pi/4`) and **computed with**
(no `ℂ`-matrix in the data). `denote : Program n → QCircuit n` is the only bridge to semantics
and the only noncomputable part.

**Design choices.**
- *Angle = `ℚ` multiples of `π`.* Exact, decidable, trivially printable, and complete for a
  discrete basis (Clifford+T is multiples of `π/4`; the QFT phase `Rk k` is `2^{1-k}·π`).
  `denote`/`toQASM` are the sole interface, so a symbolic-expression `Angle` can replace it later.
- *Operands as a bundled `Fin g.arity ↪ Fin n`.* Injectivity is intrinsic (as in `embed`/`pairEmb`),
  so `denote` is total and `denote_unitary` holds **with no `WF` hypothesis** — every program
  denotes to a unitary, the clean substrate for circuit-synthesis theorems. `Program.ofList`
  rebuilds the `↪` from a raw operand list with decidable length+`Nodup` checks (the path for
  parsed / model-emitted programs).
- *No `par`.* OpenQASM is flat; disjoint-qubit `prim`s under `seq` cover tensor placement, and
  omitting `par` keeps `denote` a clean monoid homomorphism (`denote (p*q) = denote p * denote q`,
  `denote 1 = 1`). Where a sub-block must be placed on a qubit window (e.g. the QFT's recursive
  `core ⊗ id₁`), `Program.relabel (f : Fin n ↪ Fin m)` re-addresses every gate through `f`, with
  `denote_relabel : denote (relabel f p) ≈ embed f (denote p)` bridging it to the `embed` algebra.

**Trust boundary.** `Program.toQASM` is *trusted* — we do not formalize OpenQASM's semantics.
Everything upstream is verified: `denote_unitary` unconditionally, and per-program
`denote p ≈ target` theorems (e.g. `denote_qftProgram : denote (qftProgram n) ≈ qftCircuit n`,
the acid test in `Examples/QFT.lean`) tie a syntactic program to its intended unitary.
Out of scope (v2+): measurement / classical control, hardware topology, optimization passes,
a QASM *parser*, and a computable simulator.
