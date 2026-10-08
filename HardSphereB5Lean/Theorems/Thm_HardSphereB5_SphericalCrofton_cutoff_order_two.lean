import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_cutoff_order_two
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.cutoff_order_two :
    ∀ (f : Kern), phiK f (π / 3) = 0 ∧ deriv (phiK f) (π / 3) = 0 ∧
      ∀ L, deriv (deriv (phiK f)) L = 2 * wK f (Real.cos L) * Real.sin L :=
  @proof_HardSphereB5_SphericalCrofton_cutoff_order_two
