import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_Psi_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_Psi_geometry :
    ∀ (y : Chart5) (hy : targetRegular y), sourceCenter (Psi y) = targetCenter y ∧
    sourceEndpointA (Psi y) = targetEndpointA y ∧
    sourceEndpointB (Psi y) = targetEndpointB y ∧
    (Psi y) 3 ∈ Set.Icc (-(halfA (targetCenter y))) (halfA (targetCenter y)) ∧
    (Psi y) 4 ∈ Set.Icc (-(halfB (targetCenter y))) (halfB (targetCenter y)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_Psi_geometry
