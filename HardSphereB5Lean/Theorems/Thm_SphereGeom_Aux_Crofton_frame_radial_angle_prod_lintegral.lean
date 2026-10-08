import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_frame_radial_angle_prod_lintegral
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.frame_radial_angle_prod_lintegral :
    ∀ (a b g v : E3) (hframe : Orthonormal ℝ ![a, b, g]) (hvg : inner ℝ v g = 0), (∫⁻ q : ℝ × ℝ in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (q.1 ^ 2 * |inner ℝ (Real.cos q.2 • a + Real.sin q.2 • b) v|) ∂(volume.prod volume)) = (4 / 3 : ENNReal) * ENNReal.ofReal ‖v‖ :=
  @proof_SphereGeom_Aux_Crofton_frame_radial_angle_prod_lintegral
