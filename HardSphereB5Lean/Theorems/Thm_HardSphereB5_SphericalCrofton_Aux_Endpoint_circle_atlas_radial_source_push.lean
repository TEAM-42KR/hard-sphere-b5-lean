import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_source_push
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_atlas_radial_source_push :
    ∀ (D : Pt) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C), (((volume : Measure Pt).restrict (atlasRadialSource C)).withDensity (fun x => ENNReal.ofReal |(fderiv ℝ (atlasRadial C) x).det|)).map (atlasPair C) = (3:ENNReal)⁻¹ • weightedPairMu D :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_source_push
