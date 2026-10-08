import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_nonantipodal_joined
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt) {u v : Pt}
    (hu : u ∈ greatCircle p ∩ K) (hv : v ∈ greatCircle p ∩ K)
    (huv : u ≠ -v), JoinedIn (greatCircle p ∩ K) u v :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_nonantipodal_joined
