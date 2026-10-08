import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.EA_orthonormal :
    ∀ (D : Pt) (hoff : offAxis D), Orthonormal ℝ (EA D) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
