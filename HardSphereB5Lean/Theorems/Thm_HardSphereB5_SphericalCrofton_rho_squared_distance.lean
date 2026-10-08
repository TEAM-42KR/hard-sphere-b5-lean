import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_rho_squared_distance
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.rho_squared_distance :
    ∀ (s : ℝ) (hs0 : 0 < s) (hs4 : s < 4), rhoK .one (1 - s / 2) = 4 * (s - 1) / (s * (4 - s)) ∧
      rhoK .cos (1 - s / 2) = (s - 1) * (3 - s) / (s * (4 - s)) :=
  @proof_HardSphereB5_SphericalCrofton_rho_squared_distance
