import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_fderiv_det_radial_incidence
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.fderiv_det_radial_incidence :
    ∀ (a b : ℝ → E3) (ap bp g gp : E3) (x : E3)
    (ha : HasDerivAt a ap (x 0)) (hb : HasDerivAt b bp (x 0))
    (hab : cross (a (x 0)) (b (x 0)) = g)
    (hga : inner ℝ ap g = -inner ℝ (a (x 0)) gp)
    (hgb : inner ℝ bp g = -inner ℝ (b (x 0)) gp), (fderiv ℝ (fun y : E3 => y 2 •
      (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))) x).det =
      (x 2) ^ 2 * inner ℝ (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) gp :=
  @proof_SphereGeom_Aux_Crofton_fderiv_det_radial_incidence
