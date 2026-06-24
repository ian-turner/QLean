import QLean

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

/-- `Rz(θ) followed by Rz(φ) is equivalent to Rz(θ + φ)`.
    Proof works by reducing the statement to matrix equality. --/
theorem rz_plus (θ φ : ℝ) : (RzGate φ * RzGate θ ≈ RzGate (θ + φ)) := by
  simp [RzGate, QCircuit.Equiv, QCircuit.eval, Rz]
  ring_nf
  simp [Complex.exp_add]

end

end QLean.Examples
