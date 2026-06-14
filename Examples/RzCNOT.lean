import QLean

namespace QLean.Examples

open QLean

noncomputable section

-- ── Index helpers for tensorIndexEquiv 1 1 ───────────────────────────────────

private lemma te11_symm_fst (i : Fin 4) :
    ((tensorIndexEquiv 1 1).symm i).1 = (⟨i.val % 2, by omega⟩ : Fin 2) :=
  Fin.ext (by simpa [pow_one] using tensorIndexEquiv_symm_fst_val 1 1 i)

private lemma te11_symm_snd (i : Fin 4) :
    ((tensorIndexEquiv 1 1).symm i).2 = (⟨i.val / 2, by omega⟩ : Fin 2) :=
  Fin.ext (by simpa [pow_one] using tensorIndexEquiv_symm_snd_val 1 1 i)

-- ── Explicit 4×4 form of (Rz θ) ⊗ I₂ ────────────────────────────────────────

private lemma kronQMatrix_Rz_one (θ : ℝ) :
    kronQMatrix (Rz θ) (1 : QMatrix 1) =
    !![Complex.exp (-Complex.I * θ / 2), 0, 0, 0;
       0, Complex.exp (Complex.I * θ / 2), 0, 0;
       0, 0, Complex.exp (-Complex.I * θ / 2), 0;
       0, 0, 0, Complex.exp (Complex.I * θ / 2)] := by
  ext i j
  simp only [kronQMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
             Matrix.kroneckerMap_apply]
  -- apply index lemmas after fin_cases so i,j are concrete
  fin_cases i <;> fin_cases j <;>
    simp only [te11_symm_fst, te11_symm_snd, Rz, Matrix.one_apply, Fin.ext_iff] <;>
    simp (config := { decide := true })

-- ── Rz(θ) commutes across CNOT on the control qubit ──────────────────────────

/-- Rz(θ) on qubit 0 (the CNOT control) commutes with CNOT.
    Proved by checking all four computational basis states.
    CNOT preserves qubit 0's computational basis state, so the phase that
    Rz applies is identical regardless of order. -/
theorem rz_commutes_cnot (θ : ℝ) : Circuit.Equiv
    (.seq (.par (.gate (Rz θ)) (.id : Circuit 1)) (.gate CNOT))
    (.seq (.gate CNOT) (.par (.gate (Rz θ)) (.id : Circuit 1))) := by
  rw [Circuit.Equiv.basis_iff]
  intro i; fin_cases i <;>
  simp only [eval_seq, eval_par, eval_gate, eval_id, kronQMatrix_Rz_one] <;>
  ext r c <;> fin_cases r <;> fin_cases c <;>
  simp (config := { decide := true })
    [Matrix.mul_apply, CNOT, ket,
     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end

end QLean.Examples
