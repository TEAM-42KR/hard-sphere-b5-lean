import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_phiK_nonneg
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.phiK_nonneg :
    ∀ (f : Kern) (L : ℝ) (h0 : 0 ≤ L) (h1 : L ≤ π / 3), 0 ≤ phiK f L :=
  @proof_HardSphereB5_SphericalCrofton_phiK_nonneg
