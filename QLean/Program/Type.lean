import QLean.Program.Basis
import QLean.Circuit.Semantics

/-!
# The `Program` IR and its denotation

A `Program n` is a serializable, *computable* quantum program on `n` qubits: a sequence of
named basis-gate applications, each placed at a chosen (injective) set of qubits. Unlike
`QCircuit` it stores no matrices — only `Prim` names, symbolic `Angle`s, and qubit indices —
so it serializes to OpenQASM (see `Program/QASM.lean`).

`denote : Program n → QCircuit n` (notation `⟦p⟧`, scoped in `QLean.Notation`) bridges to
the semantic layer for reasoning; it is the
*only* noncomputable part. Because every `prim` is an always-unitary named gate and its
operands form an injection, `denote_unitary` holds with **no** well-formedness hypothesis.
-/

namespace QLean

/-- A serializable quantum program on `n` qubits. `prim g qs` applies gate `g` at the qubits
    selected by the injection `qs`; `seq` sequences (rightmost runs first, matching `*` on
    circuits); `id` is the empty program. -/
inductive Program : ℕ → Type where
  | id   : Program n
  | prim : (g : Prim) → (Fin g.arity ↪ Fin n) → Program n
  | seq  : Program n → Program n → Program n

/-- `1` is the empty program. -/
instance : One (Program n) := ⟨.id⟩
/-- `p * q` sequences `q` then `p` (matrix-multiplication order: rightmost runs first). -/
instance : HMul (Program n) (Program n) (Program n) := ⟨.seq⟩

/-- Denotation into the semantic circuit layer: each `prim` becomes an embedded gate, `seq`
    becomes circuit composition, `id` becomes the identity circuit. Noncomputable (it lands
    in `QCircuit`, which carries `ℂ`-matrices); the QASM emitter never goes through it. -/
noncomputable def Program.denote : Program n → QCircuit n
  | .id        => 1
  | .prim g qs => QCircuit.embed qs (.gate g.matrix)
  | .seq p q   => p.denote * q.denote

namespace Notation

/-- `⟦p⟧` is the circuit the program `p` denotes (`Program.denote p`). Opt in with
    `open scoped QLean.Notation`. Declared `priority := high` to shadow core's `⟦·⟧`
    for `Quotient.mk` (whose explicit-`Setoid` hole elaborates against *any* expected
    type, so the two parses would otherwise be ambiguous). QLean uses no quotients;
    where one is ever needed under this scope, write `Quotient.mk _ x` explicitly. -/
scoped notation:max (priority := high) "⟦" p "⟧" => QLean.Program.denote p

end Notation

open scoped QLean.Notation

@[simp] theorem Program.denote_id : ⟦(1 : Program n)⟧ = 1 := rfl

@[simp] theorem Program.denote_prim (g : Prim) (qs : Fin g.arity ↪ Fin n) :
    ⟦Program.prim g qs⟧ = QCircuit.embed qs (.gate g.matrix) := rfl

@[simp] theorem Program.denote_seq (p q : Program n) :
    ⟦p * q⟧ = ⟦p⟧ * ⟦q⟧ := rfl

/-- The denotation of every program is well-formed: gates are always-unitary primitives and
    operands are always injective, so there is no side condition to discharge. -/
theorem Program.denote_WF : (p : Program n) → ⟦p⟧.WF
  | .id       => trivial
  | .prim g _ => g.isUnitary
  | .seq p q  => ⟨p.denote_WF, q.denote_WF⟩

/-- Every program denotes to a unitary matrix — unconditionally. -/
theorem Program.denote_unitary (p : Program n) : IsUnitary (QCircuit.eval ⟦p⟧) :=
  QCircuit.eval_unitary _ p.denote_WF

/-- Re-address a program through an injection `f`: every gate placed at qubits `qs` is moved to
    `qs.trans f`. Lifts a `Program n` to a `Program m` placed at the image of `f` (e.g. a sub-block
    onto a chosen qubit window). Denotes to the embedded denotation — see `Program/Rewrite.lean`. -/
def Program.relabel {n m : ℕ} (f : Fin n ↪ Fin m) : Program n → Program m
  | .id        => .id
  | .prim g qs => .prim g (qs.trans f)
  | .seq p q   => .seq (p.relabel f) (q.relabel f)

/-- Smart constructor: build a single-gate program from a gate and a raw operand list,
    succeeding only when the list has the gate's arity and distinct entries (both decidable).
    This is the entry point for programs assembled from data (e.g. a parser or a model). -/
def Program.ofList (g : Prim) (qs : List (Fin n)) : Option (Program n) :=
  if h : qs.length = g.arity ∧ qs.Nodup then
    some (.prim g ⟨fun i => qs.get (Fin.cast h.1.symm i),
      fun _ _ hab => Fin.cast_injective h.1.symm (List.Nodup.injective_get h.2 hab)⟩)
  else
    none

end QLean
