import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Symbolic rotation angles

A `Program`-level angle is a rational multiple of `π`. This is exact, has decidable
equality, serializes directly to OpenQASM (`1/4 ↦ "pi/4"`), and covers everything a
discrete gate basis needs: Clifford+T uses multiples of `π/4`, and the QFT phase family
`Rk k` uses `2^{1-k}·π`. The real angle it denotes is `a · π`; `denote`/`toQASM` are the
only interface, so a richer symbolic type can replace `Angle` later without touching callers.
-/

namespace QLean

/-- A rotation angle, represented as a rational multiple of `π`. `a : Angle` denotes the
    real angle `a · π` (radians). -/
abbrev Angle := ℚ

/-- The real angle (radians) denoted by `a : Angle`, namely `a · π`. -/
noncomputable def Angle.denote (a : Angle) : ℝ := (a : ℝ) * Real.pi

/-- OpenQASM rendering of `a · π`: e.g. `0 ↦ "0"`, `1 ↦ "pi"`, `1/4 ↦ "pi/4"`,
    `3/4 ↦ "3*pi/4"`, `-1/2 ↦ "-pi/2"`, `2 ↦ "2*pi"`. -/
def Angle.toQASM (a : Angle) : String :=
  if a = 0 then
    "0"
  else
    let sign    := if a.num < 0 then "-" else ""
    let absNum  := a.num.natAbs
    let numPart := if absNum = 1 then "pi" else s!"{absNum}*pi"
    let denPart := if a.den = 1 then "" else s!"/{a.den}"
    sign ++ numPart ++ denPart

end QLean
