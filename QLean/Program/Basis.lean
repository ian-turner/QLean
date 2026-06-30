import QLean.Gate.Standard
import QLean.Program.Angle

/-!
# Basis gates

`Prim` enumerates the named basis gates a `Program` may use — a *serializable* alternative
to `QCircuit.gate`, which stores an opaque `ℂ`-matrix. Each primitive has:

* `arity`     — how many qubits it acts on (computable);
* `matrix`    — its denotation as a concrete gate from `Gate/Standard.lean` (noncomputable);
* `isUnitary` — unitarity, lifted from the existing `isUnitary_*` lemmas;
* `toQASM`    — its OpenQASM mnemonic, with symbolic angle (computable).

Adding a gate is one constructor plus one line in each of those four. The basis is
Clifford+T+rotations plus what the QFT needs (`Rk`, `CRk`); `CCX`/`Sdg`/`Tdg` are easy
extensions (each needs a matching `isUnitary_*` lemma in `Gate/Standard.lean`).
-/

namespace QLean

/-- A named basis gate. Parametric rotations carry a symbolic `Angle`; the QFT phase gates
    carry their `ℕ` index. -/
inductive Prim where
  | H | X | Y | Z | S | T
  | Rz (a : Angle) | Rx (a : Angle) | Ry (a : Angle)
  | Rk (k : ℕ)
  | CX | CZ | SWAP
  | CRk (k : ℕ)
  deriving DecidableEq, Repr

/-- Number of qubits the gate acts on. -/
def Prim.arity : Prim → ℕ
  | H | X | Y | Z | S | T | Rz _ | Rx _ | Ry _ | Rk _ => 1
  | CX | CZ | SWAP | CRk _ => 2

/-- The concrete unitary a primitive denotes, drawn from `Gate/Standard.lean`. The RHS gates
    are `_root_`-qualified because a `Prim.*` definition body auto-opens the `Prim` namespace,
    which would otherwise shadow the gate names with the constructors of the same name. -/
noncomputable def Prim.matrix : (g : Prim) → QMatrix g.arity
  | H => _root_.QLean.H | X => _root_.QLean.X | Y => _root_.QLean.Y | Z => _root_.QLean.Z
  | S => _root_.QLean.S | T => _root_.QLean.T
  | Rz a => _root_.QLean.Rz (Angle.denote a)
  | Rx a => _root_.QLean.Rx (Angle.denote a)
  | Ry a => _root_.QLean.Ry (Angle.denote a)
  | Rk k => _root_.QLean.Rk k
  | CX => CNOT | CZ => _root_.QLean.CZ | SWAP => _root_.QLean.SWAP
  | CRk k => controlled (_root_.QLean.Rk k)

/-- Every basis gate is unitary: one `isUnitary_*` lemma per constructor (in declaration
    order). Each `exact` reduces `g.matrix` on its constructor to the concrete gate. -/
theorem Prim.isUnitary (g : Prim) : IsUnitary g.matrix := by
  cases g
  · exact isUnitary_H
  · exact isUnitary_X
  · exact isUnitary_Y
  · exact isUnitary_Z
  · exact isUnitary_S
  · exact isUnitary_T
  · exact isUnitary_Rz _
  · exact isUnitary_Rx _
  · exact isUnitary_Ry _
  · exact isUnitary_Rk _
  · exact isUnitary_CNOT
  · exact isUnitary_CZ
  · exact isUnitary_SWAP
  · exact isUnitary_controlled (isUnitary_Rk _)

/-- The OpenQASM phase angle of `Rk k`. Since `Rk k = diag(1, e^{2πi/2^k})` is the phase
    gate `p(2π/2^k)`, this is the rational multiple `(2/2^k)` of `π` (e.g. `R₁=p(pi)`,
    `R₂=p(pi/2)`, `R₃=p(pi/4)`). -/
def Prim.rkAngle (k : ℕ) : Angle := 2 / 2 ^ k

/-- The OpenQASM mnemonic (gate name with its symbolic parameter, if any). Operands are
    appended by the emitter, not here. -/
def Prim.toQASM : Prim → String
  | H => "h" | X => "x" | Y => "y" | Z => "z" | S => "s" | T => "t"
  | Rz a => s!"rz({Angle.toQASM a})"
  | Rx a => s!"rx({Angle.toQASM a})"
  | Ry a => s!"ry({Angle.toQASM a})"
  | Rk k => s!"p({Angle.toQASM (Prim.rkAngle k)})"
  | CX => "cx" | CZ => "cz" | SWAP => "swap"
  | CRk k => s!"cp({Angle.toQASM (Prim.rkAngle k)})"

end QLean
