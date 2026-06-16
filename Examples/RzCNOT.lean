import QLean

namespace QLean.Examples

open QLean

noncomputable section

/-- Rz(θ) on qubit 0 (the CNOT control) commutes with CNOT.
    Rz is diagonal: it applies a phase depending only on the control bit's value.
    CNOT preserves the control bit, so the phase is identical in both orderings. -/
theorem rz_commutes_cnot (θ : ℝ) :
    (RzGate θ ⊗ (1 : Circuit 1)) * CNOTGate ≈
    CNOTGate * (RzGate θ ⊗ (1 : Circuit 1)) := by
  rw [Circuit.Equiv.basis_iff]
  intro i
  obtain ⟨⟨a, b⟩, rfl⟩ := (tensorIndexEquiv 1 1).surjective i
  simp only [Circuit.eval_seq, Circuit.eval_par, Circuit.eval_gate, Circuit.eval_id, Matrix.mul_assoc]
  rw [kron_mul_ket, Matrix.one_mul, CNOT_ket_pair, kron_mul_ket, Matrix.one_mul]
  -- Goal: CNOT * tensorState (Rz θ * ket a) (ket b) = tensorState (Rz θ * ket a) (ket (a + b))
  -- Factor out the Rz diagonal phase (Rz_ket_diag), then close with CNOT_tensorState_smul_ket.
  simp only [Rz_ket_diag]
  exact CNOT_tensorState_smul_ket _ a b

end

end QLean.Examples
