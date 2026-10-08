import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_product (p p' D q : Pt) (r : ℝ)
  (hD : D = midpoint ℝ p p' + r • q) :
  inner ℝ (p - D) (NAv p p') * inner ℝ (p' - D) (NBv p p') =
    r ^ 2 * inner ℝ q (NAv p p') * inner ℝ q (NBv p p') := by
  subst D
  simp [PiLp.inner_apply, SphereGeom.cross, NAv, NBv, cross_apply,
    Fin.sum_univ_succ, midpoint_eq_smul_add]
  ring
