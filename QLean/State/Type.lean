import QLean.Basic.Matrix
import QLean.Circuit.Type

namespace QLean

/-- Symbolic expression for an `n`-qubit quantum state.
    Constructors: `basis` (computational basis ket), `smul` (scalar multiple),
    `add` (superposition), `tensor` (tensor product; qubit count adds),
    `apply` (circuit action on a state expression). -/
inductive QState : ℕ → Type where
  | basis  : Fin (2 ^ n) → QState n
  | smul   : ℂ → QState n → QState n
  | add    : QState n → QState n → QState n
  | tensor : QState j → QState k → QState (j + k)
  | apply  : Circuit n → QState n → QState n

namespace QState

/-- Transport a state expression across a propositional equality of qubit counts. -/
def castN (h : m = n) (s : QState m) : QState n := h ▸ s

instance : Add (QState n)    := ⟨.add⟩
instance : SMul ℂ (QState n) := ⟨.smul⟩
instance : HMul (Circuit n) (QState n) (QState n) := ⟨.apply⟩

-- `s ⊗ t` is the tensor product of state expressions (qubit counts sum).
infixl:70 " ⊗ " => QState.tensor

abbrev bit0 : QState 1 := .basis ⟨0, by norm_num⟩
abbrev bit1 : QState 1 := .basis ⟨1, by norm_num⟩

end QState

end QLean

namespace QLean.Notation

/-- `❘i⟩` expands to `QState.basis i`. Opt in with `open scoped QLean.Notation`.
    Uses `❘` (U+2758, LIGHT VERTICAL BAR) rather than ASCII `|` to avoid
    conflicts with Lean's pattern-match case separator and Mathlib's `∣`
    divisibility notation (U+2223). -/
scoped notation "❘" i "⟩" => QLean.QState.basis i

end QLean.Notation
