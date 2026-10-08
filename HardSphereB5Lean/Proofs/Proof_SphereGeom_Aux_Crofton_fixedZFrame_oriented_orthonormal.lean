import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
set_option autoImplicit false

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_fixedZFrame_oriented_orthonormal (p : E3) (hp : ‖p‖ = 1) (hQ : p 0 ^ 2 + p 1 ^ 2 ≠ 0) :
    Orthonormal ℝ ![fixedZA p, fixedZB p, p] ∧
      SphereGeom.cross (fixedZA p) (fixedZB p) = p := by
  have hp2 : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := by
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, hp, add_assoc] using
      (EuclideanSpace.real_norm_sq_eq p).symm
  have hr2 : fixedZRadius p ^ 2 = p 0 ^ 2 + p 1 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hr0 : fixedZRadius p ≠ 0 := by
    intro hh
    rw [hh] at hr2
    simp at hr2
    exact hQ hr2.symm
  constructor
  · apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;>
      simp [fixedZA, fixedZB, PiLp.inner_apply, Fin.sum_univ_succ]
    all_goals field_simp [hr0]
    all_goals nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2),
      congrArg (fun a : ℝ => p 2 * a) hr2]
  · ext i
    fin_cases i <;> simp [SphereGeom.cross, fixedZA, fixedZB, crossProduct]
    all_goals field_simp [hr0]
    all_goals nlinarith [congrArg (fun a : ℝ => p 2 * a) hr2]
