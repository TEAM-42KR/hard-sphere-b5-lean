import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_B (D u v : Pt) :
  ‖D - e‖ * inner ℝ (nBv D) (cross u v) =
    inner ℝ v (NBv (D + u) (D + v)) := by
  have hn : ‖D - e‖ • nBv D = e - D := by
    by_cases hD : D = e
    · simp [nBv, hD]
    · simp only [nBv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hD)), one_smul]
  rw [← real_inner_smul_left, hn]
  simp [PiLp.inner_apply, SphereGeom.cross, NBv, cross_apply, Fin.sum_univ_succ]
  ring
