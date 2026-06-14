import QLean.Circuit.Semantics
import QLean.Gate.Standard

namespace QLean

noncomputable section

-- ── Single-qubit circuit gates ────────────────────────────────────────────────

abbrev HGate : Circuit 1 := .gate H
abbrev XGate : Circuit 1 := .gate X
abbrev YGate : Circuit 1 := .gate Y
abbrev ZGate : Circuit 1 := .gate Z
abbrev SGate : Circuit 1 := .gate S
abbrev TGate : Circuit 1 := .gate T

abbrev RzGate (θ : ℝ) : Circuit 1 := .gate (Rz θ)
abbrev RxGate (θ : ℝ) : Circuit 1 := .gate (Rx θ)
abbrev RyGate (θ : ℝ) : Circuit 1 := .gate (Ry θ)

-- ── Two-qubit circuit gates ───────────────────────────────────────────────────

abbrev CNOTGate : Circuit 2 := .gate CNOT
abbrev CZGate   : Circuit 2 := .gate CZ
abbrev SWAPGate : Circuit 2 := .gate SWAP

-- ── Three-qubit circuit gate ──────────────────────────────────────────────────

abbrev ToffoliGate : Circuit 3 := .gate Toffoli

-- ── Controlled-U circuit gate ─────────────────────────────────────────────────

abbrev ControlledGate (U : QMatrix 1) : Circuit 2 := .gate (controlled U)

-- ── WF lemmas ─────────────────────────────────────────────────────────────────

@[simp] theorem wf_HGate : Circuit.WF HGate := isUnitary_H
@[simp] theorem wf_XGate : Circuit.WF XGate := isUnitary_X
@[simp] theorem wf_YGate : Circuit.WF YGate := isUnitary_Y
@[simp] theorem wf_ZGate : Circuit.WF ZGate := isUnitary_Z
@[simp] theorem wf_SGate : Circuit.WF SGate := isUnitary_S
@[simp] theorem wf_TGate : Circuit.WF TGate := isUnitary_T

@[simp] theorem wf_RzGate (θ : ℝ) : Circuit.WF (RzGate θ) := isUnitary_Rz θ
@[simp] theorem wf_RxGate (θ : ℝ) : Circuit.WF (RxGate θ) := isUnitary_Rx θ
@[simp] theorem wf_RyGate (θ : ℝ) : Circuit.WF (RyGate θ) := isUnitary_Ry θ

@[simp] theorem wf_CNOTGate : Circuit.WF CNOTGate := isUnitary_CNOT
@[simp] theorem wf_CZGate   : Circuit.WF CZGate   := isUnitary_CZ
@[simp] theorem wf_SWAPGate : Circuit.WF SWAPGate := isUnitary_SWAP

@[simp] theorem wf_ControlledGate {U : QMatrix 1} (hu : IsUnitary U) :
    Circuit.WF (ControlledGate U) := isUnitary_controlled hu

end

end QLean
