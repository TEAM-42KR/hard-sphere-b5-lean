import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_interior_chord_positive
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.interior_chord_positive :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt) (hp : ‖p‖ = 1)
    (hint : (greatCircle p ∩ sInterior K).Nonempty), 0 < chordLen K (greatCircle p) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_interior_chord_positive
