import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_hit_mass
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.hit_mass :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K), gcIntegral (fun G => if 0 < chordLen K G then 1 else 0) = perim K :=
  @proof_HardSphereB5_SphericalCrofton_hit_mass
