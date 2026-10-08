import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_single_arc_transport
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.single_arc_transport :
    ∀ {K : Set Pt} (f : Kern) (E1 E2 p : Pt) (hE : Orthonormal ℝ ![E1, E2, p]) (a b : ℝ) (hab : a ≤ b) (hπ : b - a ≤ π) (hgeom : greatCircle p ∩ K = circlePt 0 E1 E2 1 '' Set.Icc a b), (∫⁻ u in greatCircle p ∩ K, ∫⁻ v in greatCircle p ∩ K, (if (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) * ENNReal.ofReal (Real.sqrt (1 - (inner ℝ u v) ^ 2)) ∂arcMeasure ∂arcMeasure) = ENNReal.ofReal (kK f (b - a)) ∧ chordLen K (greatCircle p) = b - a :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_single_arc_transport
