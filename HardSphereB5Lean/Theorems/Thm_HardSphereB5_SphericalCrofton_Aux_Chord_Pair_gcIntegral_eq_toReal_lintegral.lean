import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_gcIntegral_eq_toReal_lintegral
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Pair.gcIntegral_eq_toReal_lintegral :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), gcIntegral (fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) = ((1 / 2 : ENNReal) * ∫⁻ p, ENNReal.ofReal ((fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) (greatCircle p)) ∂dOmega).toReal :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_gcIntegral_eq_toReal_lintegral
