# Conventions

Naming, ordering, and style decisions used throughout the library.

## Qubit ordering: LSB-first

Qubit 0 is the **least significant bit**. A 2-qubit state |q₁q₀⟩ maps to index `q₀ + q₁ * 2`.

**Why:** Mathlib's `finFunctionFinEquiv : (Fin n → Fin 2) ≃ Fin (2^n)` is LSB-first (`f ↦ ∑ i, f(i) * 2^i`). Using this directly avoids a custom equivalence and all the proofs it would require.

**Ket notation:** Write kets as |q_{n-1}…q₁q₀⟩ — MSB-first string, LSB-first index. For 2 qubits: |00⟩ = index 0, |01⟩ = index 1 (q₀=1), |10⟩ = index 2 (q₁=1), |11⟩ = index 3.

**Consequence for gate matrices:** Standard textbook matrices (MSB-first) must be reordered. For example, CNOT with control = qubit 0 (low bit) is:

```
CNOT = !![1, 0, 0, 0;
          0, 0, 0, 1;
          0, 0, 1, 0;
          0, 1, 0, 0]
```

This differs from the textbook `!![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]` (which uses control = high bit). Each multi-qubit gate in `Gate/Standard.lean` carries a comment noting its qubit roles.

## `noncomputable`

All definitions involving `ℝ`, `ℂ`, `Real.sqrt`, `Complex.exp`, or `EuclideanSpace` must be `noncomputable`. This is expected and has no practical downside for a verification library. Mark everything `noncomputable` by default in files that use these types.

## `@[simp]` set design

**Mark `@[simp]`:**
- `eval_id`, `eval_gate`, `eval_seq`, `eval_par`, `eval_castN` — unfolding rules for `eval`
- `wf_id`, `wf_gate`, `wf_seq`, `wf_par` — iff-style WF decomposition lemmas (not the constructors)
- `gateAt_one` — canonical simplification at gate-embedding boundaries

**Do not mark `@[simp]`:**
- `kron_mul` — risks looping against matrix ring lemmas
- `gateAt_mul` — use as a targeted `rw`, not a simp lemma
- `IsUnitary.*` lemmas — side conditions for explicit discharge, not simplification rules

**Intended proof idiom for `QCircuit.Equiv` goals:**
```lean
simp only [eval_seq, eval_par, eval_id, eval_gate, kron_mul]
ring   -- or norm_num for goals with Real.sqrt entries
```

## Naming

- Gate matrices: `H`, `X`, `Y`, `Z`, `S`, `T`, `CNOT`, `CZ`, `SWAP`, `Toffoli` (uppercase)
- Parametric gates: `Rz`, `Rx`, `Ry` (mixed case)
- Gate circuits (abbrevs): `HGate`, `CNOTGate`, `RzGate θ`, etc.
- Unitarity theorems: `isUnitary_H`, `isUnitary_CNOT`, `IsUnitary.kron`, etc.
- `WF` decomposition lemmas: `wf_id`, `wf_gate`, `wf_seq`, `wf_par`
- QCircuit rewrite rules (under the `QCircuit` namespace): `QCircuit.seq_id_left`, `QCircuit.par_assoc`, `QCircuit.interchange_law`

## `QVector` representation

`QVector n := Matrix (Fin (2^n)) (Fin 1) ℂ` — column matrices rather than functions or `EuclideanSpace`. This avoids all `PiLp` coercions; matrix multiplication `U * ψ` works directly.
