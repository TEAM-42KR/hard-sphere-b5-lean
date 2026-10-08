import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_radial_sq_lintegral_Ioo
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.radial_sq_lintegral_Ioo :
    (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 2)) = ENNReal.ofReal (1 / 3 : ℝ) :=
  @proof_SphereGeom_Aux_Crofton_radial_sq_lintegral_Ioo
