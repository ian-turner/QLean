import QLean.Gate.Standard
import QLean.Circuit.Rewrite

/-!
# Entrywise decision tactic for concrete circuit identities

`circuit_eq` closes a `QCircuit.Equiv` goal between circuits built from `gate`/`seq`/
`par`/`id` over concrete gates (1–3 qubits): it unfolds `eval` to a matrix identity and
checks it entrywise. `circuit_eq [l₁, l₂, …]` adds extra simp lemmas to both the main
entrywise pass and the arithmetic closer — needed e.g. for phase-gate identities whose
entries mix `Complex.exp` terms.

The `tensorIndexEquiv` ground values are introduced as local `have`s rather than global
simp lemmas: as hypotheses simp matches them against both the `OfNat` and `Fin.mk` index
forms cheaply, whereas the same facts as global lemmas send the unifier into a `whnf`
blow-up on the `Fin (2^(1+1))`-shaped literals produced by `ext`/`fin_cases`.

Defined at top level (outside all sections/namespaces) as `macro` requires; the file
imports both `Gate.Standard` (gate matrices) and `Circuit.Rewrite` (`QCircuit.Equiv`)
so every quoted name resolves here.
-/

macro "circuit_eq" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (simp only [QLean.QCircuit.Equiv, QLean.QCircuit.eval_seq, QLean.QCircuit.eval_par,
                QLean.QCircuit.eval_gate, QLean.QCircuit.eval_id]
     have t110 : (QLean.tensorIndexEquiv 1 1).symm 0 = (0, 0) := by decide
     have t111 : (QLean.tensorIndexEquiv 1 1).symm 1 = (1, 0) := by decide
     have t112 : (QLean.tensorIndexEquiv 1 1).symm 2 = (0, 1) := by decide
     have t113 : (QLean.tensorIndexEquiv 1 1).symm 3 = (1, 1) := by decide
     have t210 : (QLean.tensorIndexEquiv 2 1).symm 0 = (0, 0) := by decide
     have t211 : (QLean.tensorIndexEquiv 2 1).symm 1 = (1, 0) := by decide
     have t212 : (QLean.tensorIndexEquiv 2 1).symm 2 = (2, 0) := by decide
     have t213 : (QLean.tensorIndexEquiv 2 1).symm 3 = (3, 0) := by decide
     have t214 : (QLean.tensorIndexEquiv 2 1).symm 4 = (0, 1) := by decide
     have t215 : (QLean.tensorIndexEquiv 2 1).symm 5 = (1, 1) := by decide
     have t216 : (QLean.tensorIndexEquiv 2 1).symm 6 = (2, 1) := by decide
     have t217 : (QLean.tensorIndexEquiv 2 1).symm 7 = (3, 1) := by decide
     have t120 : (QLean.tensorIndexEquiv 1 2).symm 0 = (0, 0) := by decide
     have t121 : (QLean.tensorIndexEquiv 1 2).symm 1 = (1, 0) := by decide
     have t122 : (QLean.tensorIndexEquiv 1 2).symm 2 = (0, 1) := by decide
     have t123 : (QLean.tensorIndexEquiv 1 2).symm 3 = (1, 1) := by decide
     have t124 : (QLean.tensorIndexEquiv 1 2).symm 4 = (0, 2) := by decide
     have t125 : (QLean.tensorIndexEquiv 1 2).symm 5 = (1, 2) := by decide
     have t126 : (QLean.tensorIndexEquiv 1 2).symm 6 = (0, 3) := by decide
     have t127 : (QLean.tensorIndexEquiv 1 2).symm 7 = (1, 3) := by decide
     ext i j
     fin_cases i <;> fin_cases j <;>
       simp [QLean.H, QLean.X, QLean.Y, QLean.Z, QLean.S, QLean.T, QLean.sqrtX,
             QLean.CNOT, QLean.CZ, QLean.SWAP, QLean.sqrtSWAP, QLean.controlled,
             QLean.Toffoli, QLean.CCZ, QLean.Fredkin,
             QLean.kron, Matrix.reindex_apply, Matrix.submatrix_apply,
             Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.mul_apply,
             t110, t111, t112, t113,
             t210, t211, t212, t213, t214, t215, t216, t217,
             t120, t121, t122, t123, t124, t125, t126, t127,
             Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_eight,
             Matrix.cons_val_zero, Matrix.cons_val_one, $ts,*] <;>
       ring_nf <;>
       norm_num [QLean.sqrt2_sq_cast, Complex.I_sq, $ts,*]))

macro "circuit_eq" : tactic => `(tactic| circuit_eq [])
