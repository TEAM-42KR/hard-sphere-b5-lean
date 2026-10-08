import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_fixedZFrame_measurable
import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.fixedZFrame_measurable :
    Measurable fixedZRadius ∧ Measurable fixedZA ∧ Measurable fixedZB :=
  @proof_SphereGeom_Aux_Crofton_fixedZFrame_measurable
