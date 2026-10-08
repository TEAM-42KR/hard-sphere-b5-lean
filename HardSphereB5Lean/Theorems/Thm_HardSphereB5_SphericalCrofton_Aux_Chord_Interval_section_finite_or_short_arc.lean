import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_short_arc
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_short_arc :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (E1 E2 p : Pt)
    (hE : Orthonormal ℝ ![E1, E2, p]) (hL : chordLen K (greatCircle p) ≤ π), (greatCircle p ∩ K).Finite ∨
      ∃ a b : ℝ, a ≤ b ∧ b - a ≤ π ∧
        greatCircle p ∩ K = circlePt 0 E1 E2 1 '' Set.Icc a b :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_short_arc
