import QLean.Basic.Matrix
import Mathlib.Logic.Embedding.Basic

namespace QLean

/-- A quantum circuit on `n` qubits. `seq` constructs sequential composition,
    `par` constructs parallel composition with qubits partitioned as `j` low + `k`
    high (matching the LSB convention of `kron`), and `embed qs c` places the
    `k`-qubit sub-circuit `c` at the qubits selected by `qs : Fin k ↪ Fin n` — the
    addressing primitive for non-adjacent / reordered multi-qubit gates that plain
    `par` cannot express. -/
inductive QCircuit : ℕ → Type where
  | id    : QCircuit n
  | gate  : QMatrix n → QCircuit n
  | seq   : QCircuit n → QCircuit n → QCircuit n
  | par   : QCircuit j → QCircuit k → QCircuit (j + k)
  | embed : (Fin k ↪ Fin n) → QCircuit k → QCircuit n

/-- Transport a circuit across a propositional equality of qubit counts. -/
def QCircuit.castN (h : m = n) (c : QCircuit m) : QCircuit n := h ▸ c

-- `c₁ * c₂` sequences c₂ then c₁ (matrix-multiplication order: the rightmost factor
-- acts first); `c₁ ⊗ c₂` places them in parallel; `1` is the identity.
-- `*` has precedence 70 and `⊗` has precedence 65, so `*` binds tighter.
instance : One  (QCircuit n)                         := ⟨.id⟩
instance : HMul (QCircuit n) (QCircuit n) (QCircuit n) := ⟨.seq⟩

infixl:65 " ⊗ " => QCircuit.par

end QLean
