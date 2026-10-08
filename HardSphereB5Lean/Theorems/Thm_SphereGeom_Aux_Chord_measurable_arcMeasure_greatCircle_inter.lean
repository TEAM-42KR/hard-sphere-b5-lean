import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Chord.measurable_arcMeasure_greatCircle_inter :
    ∀ (A : Set E3) (hA : MeasurableSet A), Measurable (fun p : E3 => arcMeasure (greatCircle p ∩ A)) :=
  @proof_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter
