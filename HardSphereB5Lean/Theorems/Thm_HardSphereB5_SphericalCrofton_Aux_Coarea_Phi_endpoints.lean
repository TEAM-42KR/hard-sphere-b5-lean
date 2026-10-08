import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_endpoints
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_endpoints :
    ∀ (x : Chart5) (hA : sourceEndpointA x ∈ FA) (hB : sourceEndpointB x ∈ FB)
    (hp : |sourceEndpointA x 0| < 1) (hp' : |sourceEndpointB x 0 - 1| < 1), targetEndpointA (Phi x) = sourceEndpointA x ∧
      targetEndpointB (Phi x) = sourceEndpointB x :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_endpoints
