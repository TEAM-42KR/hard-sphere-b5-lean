import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Chord_arcMeasure_greatCircle_inter_le
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Chord.arcMeasure_greatCircle_inter_le :
    ∀ (p : E3) (hp : ‖p‖ = 1) (A : Set E3), arcMeasure (greatCircle p ∩ A) ≤ ENNReal.ofReal (2 * Real.pi) :=
  @proof_SphereGeom_Aux_Chord_arcMeasure_greatCircle_inter_le
