import QLean
import Examples.PauliAlgebra
import Examples.CliffordConjugation

/-!
# CNOT ↔ CZ conjugation identities

The Hadamard bridge between CNOT and CZ and its consequences (N&C Exercises 4.17–4.20;
Fenner Ex 11.4):

* `CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)` and `CZ = (1 ⊗ H) · CNOT · (1 ⊗ H)`
* CZ is control/target symmetric: `SWAP · CZ · SWAP = CZ`
* control/target reversal: `(H ⊗ H) · CNOT · (H ⊗ H) = CNOT-reversed`
* control-polarity flip: `(X⊗1) · CNOT · (X⊗1) · CNOT = 1 ⊗ X`

The control-split atoms (`CZGate_zero/one`, `CNOTGate_zero/one`, …) keep the target factor
symbolic, so the conjugation proofs never expand a superposition: each control value
reduces to a 1-qubit identity (`H² = 1`, `HZH = X`, `HXH = Z`) applied under the tensor.
The reversal theorem is then pure circuit-level algebra.
-/

open scoped QLean.Notation

namespace QLean.Examples

open QLean

noncomputable section

/-- The identity circuit on one qubit. -/
local notation "id1" => (1 : QCircuit 1)

-- ── 1-qubit action helpers (reassociation + a Tier-1 identity) ────────────────

/-- `H (H s) ≈ s` for any symbolic state: `h_mul_h` in action form. -/
private theorem hh_cancel (s : QState 1) : HGate * (HGate * s) ≈ s :=
  (QCircuit.seq_action _ _ _).symm.trans ((h_mul_h.apply_state s).trans (QCircuit.id_action s))

/-- `H (Z (H s)) ≈ X s`: `hzh` in action form. -/
private theorem hzh_action (s : QState 1) : HGate * (ZGate * (HGate * s)) ≈ XGate * s := by
  grw [← QCircuit.seq_action, ← QCircuit.seq_action]
  exact hzh.apply_state s

/-- `H (X (H s)) ≈ Z s`: `hxh` in action form. -/
private theorem hxh_action (s : QState 1) : HGate * (XGate * (HGate * s)) ≈ ZGate * s := by
  grw [← QCircuit.seq_action, ← QCircuit.seq_action]
  exact hxh.apply_state s

-- ── CNOT from CZ and back (N&C Ex 4.17, Fenner Ex 11.4(4)) ────────────────────

/-- `CNOT ≈ (1 ⊗ H) · CZ · (1 ⊗ H)`: conjugating the CZ target by Hadamard. -/
theorem cnot_from_cz : (id1 ⊗ HGate) * CZGate * (id1 ⊗ HGate) ≈ CNOTGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, CZGate_zero, QCircuit.par_action_tensor,
         QCircuit.id_action, hh_cancel, CNOTGate_zero]
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, CZGate_one, QCircuit.par_action_tensor,
         QCircuit.id_action, hzh_action, CNOTGate_one]

/-- `CZ ≈ (1 ⊗ H) · CNOT · (1 ⊗ H)`: the same bridge read the other way. -/
theorem cz_from_cnot : (id1 ⊗ HGate) * CNOTGate * (id1 ⊗ HGate) ≈ CZGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, CNOTGate_zero, QCircuit.par_action_tensor,
         QCircuit.id_action, hh_cancel, CZGate_zero]
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, CNOTGate_one, QCircuit.par_action_tensor,
         QCircuit.id_action, hxh_action, CZGate_one]

/-- `CNOT-reversed ≈ (H ⊗ 1) · CZ · (H ⊗ 1)`: conjugating the *other* CZ leg, using the
    target-side splits `CZGate_zero_right`/`one_right` (CZ's symmetry in atom form). -/
theorem cnotrev_from_cz : (HGate ⊗ id1) * CZGate * (HGate ⊗ id1) ≈ CNOTRevGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, CZGate_zero_right, QCircuit.par_action_tensor,
         QCircuit.id_action, hh_cancel, CNOTRevGate_basis_tensor,
         show a + 0 = a from add_zero a]
  · grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.par_action_tensor,
         QCircuit.id_action, CZGate_one_right, QCircuit.par_action_tensor,
         QCircuit.id_action, hzh_action, CNOTRevGate_basis_tensor, XGate_basis]

-- ── CZ control/target symmetry (N&C Ex 4.18) ──────────────────────────────────

/-- `SWAP · CZ · SWAP ≈ CZ`: CZ does not care which qubit is the control. -/
theorem cz_swap_symm : SWAPGate * CZGate * SWAPGate ≈ CZGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, QCircuit.seq_action, SWAPGate_tensor,
       CZGate_basis_tensor, QCircuit.apply_smul, SWAPGate_tensor,
       CZGate_basis_tensor,
       QState.smul_scalar_congr (show ((-1 : ℂ)) ^ (b.val * a.val)
          = ((-1 : ℂ)) ^ (a.val * b.val) by rw [Nat.mul_comm])]

-- ── Control/target reversal (N&C Ex 4.20, Fenner Ex 11.4(5)) ──────────────────

/-- `(H⊗H) · (1⊗H) ≈ H ⊗ 1`: fusing parallel layers with the interchange law. -/
private theorem hh_fuse_right : (HGate ⊗ HGate) * (id1 ⊗ HGate) ≈ HGate ⊗ id1 := by
  grw [← QCircuit.interchange_law, QCircuit.seq_id_right, h_mul_h]

/-- `(1⊗H) · (H⊗H) ≈ H ⊗ 1`. -/
private theorem hh_fuse_left : (id1 ⊗ HGate) * (HGate ⊗ HGate) ≈ HGate ⊗ id1 := by
  grw [← QCircuit.interchange_law, QCircuit.seq_id_left, h_mul_h]

/-- `(H ⊗ H) · CNOT · (H ⊗ H) ≈ CNOT-reversed` — control and target swap roles in the
    Hadamard basis. Proved purely at the circuit level: replace CNOT by its CZ
    conjugation, fuse the Hadamard layers, and recognize `cnotrev_from_cz`. -/
theorem cnot_reversed : (HGate ⊗ HGate) * CNOTGate * (HGate ⊗ HGate) ≈ CNOTRevGate := by
  calc (HGate ⊗ HGate) * CNOTGate * (HGate ⊗ HGate)
      ≈ (HGate ⊗ HGate) * ((id1 ⊗ HGate) * CZGate * (id1 ⊗ HGate)) * (HGate ⊗ HGate) := by
        grw [cnot_from_cz]
    _ ≈ ((HGate ⊗ HGate) * (id1 ⊗ HGate)) * CZGate * ((id1 ⊗ HGate) * (HGate ⊗ HGate)) := by
        simp only [QCircuit.Equiv, QCircuit.eval_seq, mul_assoc]
    _ ≈ (HGate ⊗ id1) * CZGate * (HGate ⊗ id1) := by
        grw [hh_fuse_right, hh_fuse_left]
    _ ≈ CNOTRevGate := cnotrev_from_cz

-- ── Control-polarity flip (N&C Figure 4.11) ───────────────────────────────────

/-- `(X⊗1) · CNOT · (X⊗1) · CNOT ≈ 1 ⊗ X`: a zero-controlled X composed with CNOT acts
    as X on the target unconditionally — the polarity-flip identity in a form that needs
    no zero-controlled gate primitive. -/
theorem cnot_polarity : (XGate ⊗ id1) * CNOTGate * (XGate ⊗ id1) * CNOTGate ≈ id1 ⊗ XGate := by
  refine (QCircuit.Equiv.basis_iff_tensor (j := 1) (k := 1) _ _).mpr fun a b => ?_
  grw [QCircuit.seq_action, QCircuit.seq_action, QCircuit.seq_action,
       CNOTGate_basis_tensor, QCircuit.par_action_tensor, QCircuit.id_action,
       XGate_basis, CNOTGate_basis_tensor, QCircuit.par_action_tensor,
       QCircuit.id_action, XGate_basis, QCircuit.par_action_tensor,
       QCircuit.id_action, XGate_basis,
       show a + 1 + 1 = a by fin_cases a <;> decide,
       show a + 1 + (a + b) = b + 1 by fin_cases a <;> fin_cases b <;> decide]

end

end QLean.Examples
