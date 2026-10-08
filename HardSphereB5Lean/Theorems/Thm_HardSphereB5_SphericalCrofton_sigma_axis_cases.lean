import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_sigma_axis_cases
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.sigma_axis_cases :
    (∀ t : ℝ, 0 < t → t < 1 → SigmaD (t • e) = ∅) ∧
      (SigmaD 0 = cap e (1 / 2) ∧ arcA 0 = ∅ ∧ arcB 0 = {u | ‖u‖ = 1 ∧ inner ℝ e u = 1 / 2}) ∧
      (SigmaD e = cap (-e) (1 / 2) ∧ arcB e = ∅ ∧
        arcA e = {u | ‖u‖ = 1 ∧ inner ℝ (-e) u = 1 / 2}) :=
  @proof_HardSphereB5_SphericalCrofton_sigma_axis_cases
