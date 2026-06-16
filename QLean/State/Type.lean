import QLean.Basic.Matrix

namespace QLean

/-- Symbolic expression for an `n`-qubit quantum state.
    Constructors: `basis` (computational basis ket), `smul` (scalar multiple),
    `add` (superposition), `tensor` (tensor product; qubit count adds). -/
inductive QState : ℕ → Type where
  | basis  : Fin (2 ^ n) → QState n
  | smul   : ℂ → QState n → QState n
  | add    : QState n → QState n → QState n
  | tensor : QState j → QState k → QState (j + k)

namespace QState

/-- Transport a state expression across a propositional equality of qubit counts. -/
def castN (h : m = n) (s : QState m) : QState n := h ▸ s

instance : Add (QState n)    := ⟨.add⟩
instance : SMul ℂ (QState n) := ⟨.smul⟩

-- `s ⊗ₛ t` is the tensor product of state expressions (qubit counts sum).
infixl:70 " ⊗ₛ " => QState.tensor

abbrev bit0 : QState 1 := .basis ⟨0, by norm_num⟩
abbrev bit1 : QState 1 := .basis ⟨1, by norm_num⟩

end QState

end QLean

namespace QLean.Notation

/-- `|i⟩` expands to `QState.basis i`. Opt in with `open scoped QLean.Notation`. -/
scoped notation "|" i "⟩" => QLean.QState.basis i

end QLean.Notation
