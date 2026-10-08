import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_chord_representation
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.chord_representation :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), Ff f K = gcIntegral (fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) :=
  @proof_HardSphereB5_SphericalCrofton_chord_representation
