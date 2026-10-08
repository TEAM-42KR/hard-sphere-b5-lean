import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_rho_rational
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.rho_rational :
    ∀ (f : Kern) (δ : ℝ), deriv (phiK f) δ / (1 - Real.cos δ ^ 2) = rhoK f (Real.cos δ) :=
  @proof_HardSphereB5_SphericalCrofton_rho_rational
