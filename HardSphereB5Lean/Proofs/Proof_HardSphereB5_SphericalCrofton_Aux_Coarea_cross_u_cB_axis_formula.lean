import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.MovingArc
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_cross_u_cB_axis_formula (D : Pt) (α : ℝ) :
    inner ℝ (SphereGeom.cross (u D α) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)) e =
      rA D * Real.sin α * (D 1 ^ 2 + D 2 ^ 2) / (2 * ‖D‖ * ‖rawA D‖) := by
  simp [u, circlePt, EA, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA,
    HardSphereB5.SphericalCrofton.Aux.MovingArc.cB, unitDir, rawA, nAv,
    SphereGeom.cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_succ, e,
    div_eq_mul_inv, mul_inv_rev, Matrix.vecHead, Matrix.vecTail]
  ring
