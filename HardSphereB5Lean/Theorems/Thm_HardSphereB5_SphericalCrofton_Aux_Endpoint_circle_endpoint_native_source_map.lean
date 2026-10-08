import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_native_source_map
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_endpoint_native_source_map :
    ∀ (C : CircleEndpointAtlas)
    (hE : ∀ i, Orthonormal ℝ (C.frame i)) (hr : ∀ i, 0 < C.r i)
    (hT0 : ∀ i, 0 ≤ C.T i) (hT : ∀ i, C.T i ≤ 2*Real.pi)
    (hdisjoint : Disjoint (atlasCircle C 0 '' Set.Ioo 0 (C.T 0))
      (atlasCircle C 1 '' Set.Ioo 0 (C.T 1))), (atlasSourceMu C).map (atlasGamma C) =
      arcMeasure.restrict ((atlasCircle C 0 '' Set.Ioo 0 (C.T 0)) ∪
        (atlasCircle C 1 '' Set.Ioo 0 (C.T 1))) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_native_source_map
