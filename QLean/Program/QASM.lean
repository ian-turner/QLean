import QLean.Program.Type

/-!
# OpenQASM 3.0 emission

`Program.toQASM` compiles a program to an OpenQASM 3.0 source string. It is fully
*computable* and reads only gate names, symbolic angles, and qubit indices — never a matrix,
never `denote`. We do not formalize OpenQASM's semantics, so the emitter is trusted; what is
verified is everything upstream of it (`denote_unitary`, and per-program `p ⇓ target`
theorems).
-/

namespace QLean

/-- An OpenQASM qubit operand, `q[i]`. -/
def qasmQubit (i : Fin n) : String := s!"q[{i.val}]"

/-- The OpenQASM line for a single gate application: mnemonic, comma-separated operands,
    semicolon. Gate-qubit `i` maps to physical qubit `qs i`. -/
def Program.instrLine (g : Prim) (qs : Fin g.arity ↪ Fin n) : String :=
  let args := (List.finRange g.arity).map (fun i => qasmQubit (qs i))
  s!"{g.toQASM} {String.intercalate ", " args};"

/-- Body lines in execution order (earliest-run first). `seq p q` runs `q` first (rightmost
    acts first, matching `*`), so `q`'s lines precede `p`'s. -/
def Program.bodyLines : Program n → List String
  | .id        => []
  | .prim g qs => [Program.instrLine g qs]
  | .seq p q   => q.bodyLines ++ p.bodyLines

/-- Compile a program to an OpenQASM 3.0 program string. -/
def Program.toQASM {n : ℕ} (p : Program n) : String :=
  String.intercalate "\n"
    (["OPENQASM 3.0;", "include \"stdgates.inc\";", s!"qubit[{n}] q;"] ++ p.bodyLines)

end QLean
