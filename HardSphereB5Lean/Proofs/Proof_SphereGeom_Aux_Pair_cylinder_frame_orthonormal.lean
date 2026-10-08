import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_Aux_Pair_cylinder_frame_orthonormal (z φ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    Orthonormal ℝ ![
      (WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0] : E3),
      (WithLp.toLp 2 ![-z * Real.cos φ, -z * Real.sin φ, Real.sqrt (1-z^2)] : E3),
      (WithLp.toLp 2 ![Real.sqrt (1-z^2) * Real.cos φ, Real.sqrt (1-z^2) * Real.sin φ, z] : E3)] := by
  have hs : Real.sqrt (1-z^2)^2 = 1-z^2 := Real.sq_sqrt (by nlinarith [hz.1, hz.2])
  have ht := Real.cos_sq_add_sin_sq φ
  apply orthonormal_iff_ite.mpr
  intro i j
  simp only [PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ]
  all_goals nlinarith [sq_nonneg z, sq_nonneg (Real.cos φ), sq_nonneg (Real.sin φ),
    congrArg (fun a : ℝ => z^2*a) ht,
    congrArg (fun a : ℝ => Real.sqrt (1-z^2)^2*a) ht,
    congrArg (fun a : ℝ => z*Real.sqrt (1-z^2)*a) ht]
