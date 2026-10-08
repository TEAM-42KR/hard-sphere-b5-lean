import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_ae_radial_of_ae_spherical
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.ae_radial_of_ae_spherical :
    ∀ (P : Pt → Prop) (hP : ∀ᵐ p ∂dOmega, P p), ∀ᵐ y ∂((volume : Measure Pt).restrict (Metric.ball (0:Pt) 1)), P (‖y‖⁻¹ • y) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_ae_radial_of_ae_spherical
