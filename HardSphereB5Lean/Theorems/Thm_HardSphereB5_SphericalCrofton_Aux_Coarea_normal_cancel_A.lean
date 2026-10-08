import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_A
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.normal_cancel_A :
    ∀ (D u v : Pt), ‖D‖ * inner ℝ (nAv D) (cross u v) =
    inner ℝ u (NAv (D + u) (D + v)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_A
