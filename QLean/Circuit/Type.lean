import QLean.Basic.Matrix

namespace QLean

/-- A quantum circuit on `n` qubits. `par` constructs parallel composition with
    qubits partitioned as `j` low + `k` high, matching the LSB convention of `kron`. -/
inductive Circuit : ℕ → Type where
  | id   : Circuit n
  | gate : QMatrix n → Circuit n
  | seq  : Circuit n → Circuit n → Circuit n
  | par  : Circuit j → Circuit k → Circuit (j + k)

/-- Transport a circuit across a propositional equality of qubit counts. -/
def Circuit.castN (h : m = n) (c : Circuit m) : Circuit n := h ▸ c

-- `c₁ * c₂` sequences c₁ then c₂; `c₁ + c₂` places them in parallel; `1` is the identity.
-- `*` has precedence 70 and `+` has precedence 65, so `*` binds tighter.
instance : One     (Circuit n)                          := ⟨.id⟩
instance : HMul    (Circuit n) (Circuit n) (Circuit n)  := ⟨.seq⟩
instance : HAdd    (Circuit j) (Circuit k) (Circuit (j + k)) := ⟨.par⟩

end QLean
