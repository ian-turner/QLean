import QLean

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

/-- The identity circuit on one qubit; a space-saving alias for `(1 : Circuit 1)`. -/
abbrev id1 : Circuit 1 := 1

/-- `Rz(θ)` on qubit 0 (the CNOT control) commutes with CNOT.

    The argument is equational reasoning in the symbolic state layer. By
    `Circuit.Equiv.basis_iff_tensor` it suffices to check both circuit orderings on
    every factored basis state `❘a⟩ ⊗ₛ ❘b⟩`, and we show they land on the *same*
    phased state `φ • (❘a⟩ ⊗ₛ ❘a+b⟩)`:

    * Rz is diagonal, so on the control ket `❘a⟩` it is just multiplication by some
      phase `φ` — we keep `φ` abstract, since its value is irrelevant to commutativity.
    * `Rz ⊗ 1` therefore phases any basis tensor with control `❘a⟩` by `φ`, leaving the
      target ket untouched (`rz_phase`).
    * CNOT flips the target and preserves the control (`CNOTGate_basis_tensor`).

    Running the two gates in either order phases by the same `φ` (it depends only on the
    control, which CNOT never changes) and flips the target once, so the results agree. -/
theorem rz_commutes_cnot (θ : ℝ) :
    (RzGate θ ⊗ id1) * CNOTGate ≈ CNOTGate * (RzGate θ ⊗ id1) := by
  refine (Circuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  -- Rz acts as a scalar `φ` on the control ket; we never need φ's actual value.
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ, RzGate θ * ❘a⟩ ≈ φ • ❘a⟩ := ⟨_, RzGate_basis θ a⟩
  -- `Rz ⊗ 1` phases any basis tensor with control `❘a⟩` by `φ`, whatever the target ket.
  -- `grw` is `rw` modulo `≈`: it rewrites under the tensor/smul congruences automatically.
  have rz_phase : ∀ x : Fin (2 ^ 1),
      (RzGate θ ⊗ id1) * (❘a⟩ ⊗ₛ ❘x⟩) ≈ φ • (❘a⟩ ⊗ₛ ❘x⟩) := fun x => by
    grw [Circuit.par_action_tensor, hφ, Circuit.id_action, QState.smul_tensor_left]
  -- Ordering 1 — phase the control, then flip the target.
  have order₁ : ((RzGate θ ⊗ id1) * CNOTGate) * (❘a⟩ ⊗ₛ ❘b⟩) ≈ φ • (❘a⟩ ⊗ₛ ❘a + b⟩) := by
    grw [Circuit.seq_action, rz_phase b, Circuit.apply_smul, CNOTGate_basis_tensor]
  -- Ordering 2 — flip the target, then phase the (unchanged) control.
  have order₂ : (CNOTGate * (RzGate θ ⊗ id1)) * (❘a⟩ ⊗ₛ ❘b⟩) ≈ φ • (❘a⟩ ⊗ₛ ❘a + b⟩) := by
    grw [Circuit.seq_action, CNOTGate_basis_tensor, rz_phase (a + b)]
  -- Both orderings reach the same phased state.
  exact order₁.trans order₂.symm

end

end QLean.Examples
