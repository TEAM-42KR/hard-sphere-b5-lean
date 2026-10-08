import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_centerFrame_nonzero
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_centerFrame_nonzero :
    ∀ (y : Chart5) (h0 : |y 0| < 1) (h2 : |y 2| < 1)
    (h1 : y 1 ∈ Set.Ioo (-Real.pi) Real.pi) (h3 : y 3 ∈ Set.Ioo (-Real.pi) Real.pi)
    (h13 : y 1 ≠ y 3), centerFrame0 (targetEndpointB y-targetEndpointA y) ≠ 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_centerFrame_nonzero
