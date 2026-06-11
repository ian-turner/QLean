import QLean.Basic.Matrix

namespace QLean

/-- A quantum circuit on `n` qubits. `par` constructs parallel composition with
    qubits partitioned as `j` low + `k` high, matching the LSB convention of `kronQMatrix`. -/
inductive Circuit : ℕ → Type where
  | id   : Circuit n
  | gate : QMatrix n → Circuit n
  | seq  : Circuit n → Circuit n → Circuit n
  | par  : Circuit j → Circuit k → Circuit (j + k)

/-- Transport a circuit across a propositional equality of qubit counts. -/
def Circuit.castN (h : m = n) (c : Circuit m) : Circuit n := h ▸ c

end QLean
