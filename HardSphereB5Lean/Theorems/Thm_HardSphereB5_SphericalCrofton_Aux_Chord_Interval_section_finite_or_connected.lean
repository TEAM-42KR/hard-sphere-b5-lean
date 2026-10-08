import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_connected
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_connected :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt), (greatCircle p ∩ K).Finite ∨ IsConnected (greatCircle p ∩ K) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_connected
