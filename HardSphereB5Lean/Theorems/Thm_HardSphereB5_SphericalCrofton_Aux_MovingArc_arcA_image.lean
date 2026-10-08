import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_arcA_image
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.arcA_image :
    ∀ (D : Pt)
  (hL : D ∈ LamC) (hoff : offAxis D) (hRc : Rc ‖D‖ ‖D-e‖ < 1), arcA D = HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-(halfA D)) (halfA D) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_arcA_image
