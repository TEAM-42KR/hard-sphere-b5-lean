import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_regular
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_atlas_radial_regular :
    ∀ (D : Pt) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C), Measurable (atlasRadial C) ∧ Measurable (fderiv ℝ (atlasRadial C)) ∧ Measurable (atlasPair C) ∧ MeasurableSet (atlasRadialSource C) ∧ (∀ x ∈ atlasRadialSource C, HasFDerivWithinAt (atlasRadial C) (fderiv ℝ (atlasRadial C) x) (atlasRadialSource C) x) ∧ (∀ x ∈ atlasRadialSource C, ‖atlasRadial C x‖⁻¹ • atlasRadial C x = pairPole (atlasPair C x)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_regular
