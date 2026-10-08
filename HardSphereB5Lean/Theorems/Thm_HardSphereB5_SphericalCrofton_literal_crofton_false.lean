import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_literal_crofton_false
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.literal_crofton_false :
    ∀ (n : Pt) (hn : ‖n‖ = 1) (f : Kern), Ff f (cap n (Real.cos (π / 6))) ≠
      cA f * sArea (cap n (Real.cos (π / 6))) - cP f * perim (cap n (Real.cos (π / 6)))
        + RfAll f (cap n (Real.cos (π / 6))) :=
  @proof_HardSphereB5_SphericalCrofton_literal_crofton_false
