import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_endpointsA_width
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.MovingArc SphereGeom

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA_width :
    ∀ (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) (hRc : Rc ‖D‖ ‖D - e‖ < 1), dist (u D (-(halfA D))) (u D (halfA D)) = 2 * rA D * Real.sin (halfA D) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_endpointsA_width
