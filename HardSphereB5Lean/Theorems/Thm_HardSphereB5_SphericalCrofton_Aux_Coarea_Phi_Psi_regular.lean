import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_Psi_regular
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_Psi_regular :
    ∀ (y : Chart5) (hy : targetRegular y), Phi (Psi y) = y ∧ sourceRegular (Psi y) ∧
    Rc ‖sourceCenter (Psi y)‖ ‖sourceCenter (Psi y)-e‖ < 1 ∧
    (Psi y) 3 ∈ Set.Icc (-(halfA (sourceCenter (Psi y)))) (halfA (sourceCenter (Psi y))) ∧
    (Psi y) 4 ∈ Set.Icc (-(halfB (sourceCenter (Psi y)))) (halfB (sourceCenter (Psi y))) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_Psi_regular
