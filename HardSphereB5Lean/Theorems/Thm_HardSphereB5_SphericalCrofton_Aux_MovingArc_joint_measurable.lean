import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_joint_measurable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.joint_measurable :
    Measurable (fun x : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.u x.1 x.2) ∧
    Measurable (fun x : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.v x.1 x.2) ∧
    Measurable HardSphereB5.SphericalCrofton.Aux.MovingArc.halfA ∧
    Measurable HardSphereB5.SphericalCrofton.Aux.MovingArc.halfB :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_joint_measurable
