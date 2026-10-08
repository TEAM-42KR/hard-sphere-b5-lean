import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_oriented_fiber
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_atlas_oriented_fiber :
    ∀ (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C) (F : Set Pt) (hcover : atlasGamma C '' atlasInterval C = sFrontier (SigmaD D) \ F) (p : Pt) (hp : ‖p‖ = 1) (havoid : greatCircle p ∩ F = ∅) (hcard : ((greatCircle p ∩ sFrontier (SigmaD D)).encard : ENNReal) = if p ∈ hitPoleSet D then 2 else 0) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1), ({x : Pt | x ∈ atlasRadialSource C ∧ atlasRadial C x = r • p}.encard : ENNReal) = if p ∈ hitPoleSet D then 1 else 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_oriented_fiber
