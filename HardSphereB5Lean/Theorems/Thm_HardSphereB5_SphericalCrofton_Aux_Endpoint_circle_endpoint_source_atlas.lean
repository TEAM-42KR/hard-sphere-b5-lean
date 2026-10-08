import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_source_atlas
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_endpoint_source_atlas :
    ∀ (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)), ∃ C : CircleEndpointAtlas, IsCircleEndpointAtlas D C :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_source_atlas
