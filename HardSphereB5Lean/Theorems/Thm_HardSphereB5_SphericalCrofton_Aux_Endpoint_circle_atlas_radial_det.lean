import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_det
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_atlas_radial_det :
    ∀ (D : Pt) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C) (x : Pt) (hx : x ∈ atlasRadialSource C), |(fderiv ℝ (atlasRadial C) x).det| = (x 2)^2 * atlasSpeed C (x 0) * atlasSpeed C (x 1) * pairDens D (atlasPair C x) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_det
