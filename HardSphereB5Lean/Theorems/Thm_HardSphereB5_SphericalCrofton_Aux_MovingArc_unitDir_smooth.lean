import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_unitDir_smooth
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.unitDir_smooth :
    ∀ (x : Pt) (hx : x ≠ 0), ContDiffAt ℝ ⊤ unitDir x :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_unitDir_smooth
