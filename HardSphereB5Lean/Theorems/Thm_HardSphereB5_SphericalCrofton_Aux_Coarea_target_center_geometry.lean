import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_center_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_center_geometry :
    ∀ (y : Chart5)
    (hz0 : 0 < dist (targetEndpointA y) (targetEndpointB y))
    (hz2 : dist (targetEndpointA y) (targetEndpointB y) < 2)
    (hf : centerFrame0 (targetEndpointB y-targetEndpointA y) ≠ 0)
    (hψ : y 4 ∈ Set.Ioo (-Real.pi) Real.pi), dist (targetCenter y) (targetEndpointA y) = 1 ∧
    dist (targetCenter y) (targetEndpointB y) = 1 ∧
    Complex.arg (centerPhase (targetCenter y) (targetEndpointA y) (targetEndpointB y)) = y 4 ∧
    centerPhase (targetCenter y) (targetEndpointA y) (targetEndpointB y) ∈ Complex.slitPlane :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_center_geometry
