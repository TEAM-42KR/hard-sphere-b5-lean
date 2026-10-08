import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_kernel_constants
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.kernel_constants :
    alphaK .one = 1 ∧ bK .one = √3 - π / 3 ∧ alphaK .cos = 3 / 4 ∧ bK .cos = √3 / 8 + π / 12 ∧
      (∀ f, cA f = π * alphaK f ∧ cP f = bK f) :=
  @proof_HardSphereB5_SphericalCrofton_kernel_constants
