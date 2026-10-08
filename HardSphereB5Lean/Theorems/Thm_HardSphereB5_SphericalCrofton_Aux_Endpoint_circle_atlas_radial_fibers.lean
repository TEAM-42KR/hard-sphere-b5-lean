import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_fibers
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_atlas_radial_fibers :
    ∀ (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C), MeasurableSet (hitPoleSet D) ∧ (∀ᵐ y ∂(volume : Measure Pt), ({x : Pt | x ∈ atlasRadialSource C ∧ atlasRadial C x = y}.encard : ENNReal) = (Metric.ball (0:Pt) 1 ∩ (fun y : Pt => ‖y‖⁻¹ • y) ⁻¹' hitPoleSet D).indicator (fun _ => (1:ENNReal)) y) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_fibers
