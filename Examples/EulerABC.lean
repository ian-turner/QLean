import QLean
import Examples.PauliAlgebra
import Examples.RotationIdentities
import Examples.RzPlus

/-!
# The ABC decomposition (equational core of N&C Corollary 4.2)

For Euler angles `β γ δ`, define

* `A = Rz(β) · Ry(γ/2)`
* `B = Ry(−γ/2) · Rz(−(δ+β)/2)`
* `C = Rz((δ−β)/2)`

Then `A·B·C ≈ 1` and `A·X·B·X·C ≈ Rz(β)·Ry(γ)·Rz(δ)` — so any unitary with Euler
decomposition `e^{iα} Rz(β) Ry(γ) Rz(δ)` (Theorem 4.1) can be written `e^{iα} A·X·B·X·C`
with `A·B·C = 1`, which is exactly what the controlled-U construction (N&C Figure 4.6)
needs: the target sees `U` when the control is set and `ABC = 1` when it is not.

Everything here is *circuit-level* `grw` rewriting: the only ingredients are rotation
additivity (`ry_plus`, `rz_plus`), the zero rotations, and the X-conjugation identities
`X·Ry(θ)·X ≈ Ry(−θ)`, `X·Rz(θ)·X ≈ Rz(−θ)`. The `calc` steps that merely re-associate
`*` are discharged by unfolding `eval` to the matrix monoid (`simp only [… mul_assoc]`).
-/

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

/-- `A = Rz(β) · Ry(γ/2)`. -/
def eulerA (β γ : ℝ) : QCircuit 1 := RzGate β * RyGate (γ/2)

/-- `B = Ry(−γ/2) · Rz(−(δ+β)/2)`. -/
def eulerB (β γ δ : ℝ) : QCircuit 1 := RyGate (-(γ/2)) * RzGate (-((δ+β)/2))

/-- `C = Rz((δ−β)/2)`. -/
def eulerC (β δ : ℝ) : QCircuit 1 := RzGate ((δ-β)/2)

/-- `A · B · C ≈ 1`: with the X's removed, the three factors cancel. -/
theorem euler_abc_cancel (β γ δ : ℝ) :
    eulerA β γ * eulerB β γ δ * eulerC β δ ≈ (1 : QCircuit 1) := by
  calc eulerA β γ * eulerB β γ δ * eulerC β δ
      ≈ RzGate β * (RyGate (γ/2) * RyGate (-(γ/2)))
          * (RzGate (-((δ+β)/2)) * RzGate ((δ-β)/2)) := by
        simp only [eulerA, eulerB, eulerC, QCircuit.Equiv, QCircuit.eval_seq, mul_assoc]
    _ ≈ RzGate β * RyGate (-(γ/2) + γ/2) * RzGate ((δ-β)/2 + -((δ+β)/2)) := by
        grw [ry_plus, rz_plus]
    _ ≈ RzGate β * RyGate 0 * RzGate (-β) := by
        rw [show -(γ/2) + γ/2 = 0 by ring, show (δ-β)/2 + -((δ+β)/2) = -β by ring]
    _ ≈ RzGate β * RzGate (-β) := by
        grw [ry_zero, QCircuit.seq_id_right]
    _ ≈ RzGate (-β + β) := rz_plus (-β) β
    _ ≈ RzGate 0 := by rw [show -β + β = 0 by ring]
    _ ≈ (1 : QCircuit 1) := rz_zero

/-- `X · B · X ≈ Ry(γ/2) · Rz((δ+β)/2)`: conjugating `B` by X flips both its angles
    (N&C eq. 4.16). -/
theorem euler_xbx (β γ δ : ℝ) :
    XGate * eulerB β γ δ * XGate ≈ RyGate (γ/2) * RzGate ((δ+β)/2) := by
  have X_mm : (X : QMatrix 1) * X = 1 := x_mul_x
  calc XGate * eulerB β γ δ * XGate
      ≈ (XGate * RyGate (-(γ/2)) * XGate) * (XGate * RzGate (-((δ+β)/2)) * XGate) := by
        simp only [eulerB, QCircuit.Equiv, QCircuit.eval_seq, QCircuit.eval_gate, mul_assoc]
        rw [show (X : QMatrix 1) * (X * (Rz (-((δ+β)/2)) * X)) = Rz (-((δ+β)/2)) * X by
          rw [← mul_assoc, X_mm, one_mul]]
    _ ≈ RyGate (-(-(γ/2))) * RzGate (-(-((δ+β)/2))) := by
        grw [x_ry_x, x_rz_x]
    _ ≈ RyGate (γ/2) * RzGate ((δ+β)/2) := by
        rw [neg_neg, neg_neg]

/-- The ABC decomposition: `A·X·B·X·C ≈ Rz(β)·Ry(γ)·Rz(δ)` (the Euler product whose
    phase-augmented form is any single-qubit unitary, N&C Theorem 4.1/Corollary 4.2). -/
theorem euler_abc_x_decomposition (β γ δ : ℝ) :
    eulerA β γ * XGate * eulerB β γ δ * XGate * eulerC β δ
      ≈ RzGate β * RyGate γ * RzGate δ := by
  calc eulerA β γ * XGate * eulerB β γ δ * XGate * eulerC β δ
      ≈ eulerA β γ * (XGate * eulerB β γ δ * XGate) * eulerC β δ := by
        simp only [QCircuit.Equiv, QCircuit.eval_seq, mul_assoc]
    _ ≈ eulerA β γ * (RyGate (γ/2) * RzGate ((δ+β)/2)) * eulerC β δ := by
        grw [euler_xbx]
    _ ≈ RzGate β * (RyGate (γ/2) * RyGate (γ/2))
          * (RzGate ((δ+β)/2) * RzGate ((δ-β)/2)) := by
        simp only [eulerA, eulerC, QCircuit.Equiv, QCircuit.eval_seq, mul_assoc]
    _ ≈ RzGate β * RyGate (γ/2 + γ/2) * RzGate ((δ-β)/2 + (δ+β)/2) := by
        grw [ry_plus, rz_plus]
    _ ≈ RzGate β * RyGate γ * RzGate δ := by
        rw [show γ/2 + γ/2 = γ by ring, show (δ-β)/2 + (δ+β)/2 = δ by ring]

end

end QLean.Examples
