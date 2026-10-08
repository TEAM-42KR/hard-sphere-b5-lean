import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_spherical_remainder_split
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.spherical_remainder_split :
    ∀ (f : Kern) (D : Pt) (hD : D ∈ LamC), Rf f (SigmaD D) = AAf f D + BBf f D + ABf f D :=
  @proof_HardSphereB5_SphericalCrofton_spherical_remainder_split
