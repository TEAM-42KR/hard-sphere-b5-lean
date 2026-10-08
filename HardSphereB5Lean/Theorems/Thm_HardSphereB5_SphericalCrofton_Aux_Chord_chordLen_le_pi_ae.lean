import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_chordLen_le_pi_ae
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.chordLen_le_pi_ae :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K), ∀ᵐ p ∂dOmega, chordLen K (greatCircle p) ≤ π :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_chordLen_le_pi_ae
