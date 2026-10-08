import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Chord_arcMeasure_greatCircle_closedHemisphere
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Chord.arcMeasure_greatCircle_closedHemisphere :
    ∀ (n p : E3) (hn : ‖n‖ = 1) (hp : ‖p‖ = 1) (hpn : p ≠ n) (hpnm : p ≠ -n), arcMeasure (greatCircle p ∩ {u : E3 | 0 ≤ inner ℝ n u}) = ENNReal.ofReal Real.pi :=
  @proof_SphereGeom_Aux_Chord_arcMeasure_greatCircle_closedHemisphere
