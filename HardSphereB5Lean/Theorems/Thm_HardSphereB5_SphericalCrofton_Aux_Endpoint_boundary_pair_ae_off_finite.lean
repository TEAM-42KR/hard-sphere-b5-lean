import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_pair_ae_off_finite
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.boundary_pair_ae_off_finite :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (F : Set Pt) (hF : F.Finite) (hFu : ∀ u ∈ F, ‖u‖ = 1), ∀ᵐ p ∂dOmega, ‖p‖ = 1 ∧ greatCircle p ∩ F = ∅ ∧ ((greatCircle p ∩ sFrontier K).encard : ENNReal) = if 0 < chordLen K (greatCircle p) then 2 else 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_pair_ae_off_finite
