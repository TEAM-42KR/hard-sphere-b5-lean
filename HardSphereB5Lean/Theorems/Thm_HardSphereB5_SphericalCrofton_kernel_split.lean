import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_kernel_split
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.kernel_split :
    ∀ (f : Kern) (L : ℝ) (h0 : 0 ≤ L) (hπ : L ≤ π), kK f L = alphaK f * L - bK f + (if L < π / 3 then phiK f L else 0) :=
  @proof_HardSphereB5_SphericalCrofton_kernel_split
