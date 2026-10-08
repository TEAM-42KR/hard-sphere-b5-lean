import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_oriented_deriv_A
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.oriented_deriv_A :
    ∀ (D : Pt) (hoff : offAxis D) (t : ℝ), HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D)
    (cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t)) t :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_oriented_deriv_A
