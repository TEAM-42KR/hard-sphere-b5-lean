import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_joint_measurable :
    Measurable (fun x : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.u x.1 x.2) ∧
    Measurable (fun x : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.v x.1 x.2) ∧
    Measurable HardSphereB5.SphericalCrofton.Aux.MovingArc.halfA ∧
    Measurable HardSphereB5.SphericalCrofton.Aux.MovingArc.halfB := by
  unfold HardSphereB5.SphericalCrofton.Aux.MovingArc.u HardSphereB5.SphericalCrofton.Aux.MovingArc.v
    HardSphereB5.SphericalCrofton.Aux.MovingArc.halfA HardSphereB5.SphericalCrofton.Aux.MovingArc.halfB
    HardSphereB5.SphericalCrofton.Aux.MovingArc.cutA HardSphereB5.SphericalCrofton.Aux.MovingArc.cutB
    HardSphereB5.SphericalCrofton.Aux.MovingArc.cA HardSphereB5.SphericalCrofton.Aux.MovingArc.cB
    HardSphereB5.SphericalCrofton.Aux.MovingArc.rA HardSphereB5.SphericalCrofton.Aux.MovingArc.rB
    HardSphereB5.SphericalCrofton.Aux.MovingArc.EA HardSphereB5.SphericalCrofton.Aux.MovingArc.EB
    HardSphereB5.SphericalCrofton.Aux.MovingArc.rawA HardSphereB5.SphericalCrofton.Aux.MovingArc.rawB
    circlePt unitDir nAv nBv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · unfold cross
    apply Measurable.add <;> fun_prop
  constructor
  · unfold cross
    apply Measurable.add <;> fun_prop
  constructor <;> fun_prop
