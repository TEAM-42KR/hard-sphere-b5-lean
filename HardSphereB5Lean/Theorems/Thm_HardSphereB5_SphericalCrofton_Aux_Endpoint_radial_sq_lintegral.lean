import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_sq_lintegral
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.radial_sq_lintegral :
    (∫⁻ r in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (r^2)) = (3:ENNReal)⁻¹ :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_sq_lintegral
