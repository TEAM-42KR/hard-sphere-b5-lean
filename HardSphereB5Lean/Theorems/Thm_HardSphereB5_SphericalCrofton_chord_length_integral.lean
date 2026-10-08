import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_chord_length_integral
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.chord_length_integral :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K), gcIntegral (fun G => if 0 < chordLen K G then chordLen K G else 0) = π * sArea K :=
  @proof_HardSphereB5_SphericalCrofton_chord_length_integral
