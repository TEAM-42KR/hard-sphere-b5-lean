import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_u_smooth
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.u_smooth :
    ∀ (D : Pt) (t : ℝ)
    (hD : D ≠ 0) (hr : ‖D‖ < 2) (hA : HardSphereB5.SphericalCrofton.Aux.MovingArc.rawA D ≠ 0), ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.u x.1 x.2) (D,t) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_u_smooth
