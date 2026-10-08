import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_A (D u v : Pt) :
  ‖D‖ * inner ℝ (nAv D) (cross u v) =
    inner ℝ u (NAv (D + u) (D + v)) := by
  have hn : ‖D‖ • nAv D = -D := by
    by_cases hD : D = 0
    · simp [nAv, hD]
    · simp only [nAv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD), one_smul]
  rw [← real_inner_smul_left, hn]
  simp [PiLp.inner_apply, SphereGeom.cross, NAv, cross_apply, Fin.sum_univ_succ]
  ring
