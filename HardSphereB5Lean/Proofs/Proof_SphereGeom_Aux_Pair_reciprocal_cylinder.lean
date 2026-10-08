import HardSphereB5Lean.Definitions.Def_SphereGeom_Aux_Pair_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom SphereGeom.Aux.Pair
theorem proof_SphereGeom_Aux_Pair_reciprocal_cylinder (w α ψ : ℝ) (hw : w^2 < 1) :
    reciprocal (SphereGeom.Aux.Pair.cylinder w α) ψ = fiber w ψ α := by
  have hd : Real.sqrt (1-w^2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  simp only [reciprocal, SphereGeom.Aux.Pair.cylinder, fiber, circlePt, zero_add, one_smul]
  change ((Real.sqrt (1-w^2) * Real.cos α) / Real.sqrt (1-w^2)) • frame1 ψ +
    ((Real.sqrt (1-w^2) * Real.sin α) / Real.sqrt (1-w^2)) • frame2 w ψ =
    Real.cos α • frame1 ψ + Real.sin α • frame2 w ψ
  rw [mul_div_cancel_left₀ _ hd, mul_div_cancel_left₀ _ hd]
