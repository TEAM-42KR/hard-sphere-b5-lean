import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem phi_one_deriv (x : ℝ) : deriv (phiK .one) x = 1 - 2 * Real.cos x := by
  have hd : HasDerivAt (phiK .one) (1 - 2 * Real.cos x) x := by
    convert (((hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).const_mul 2)).add_const (Real.sqrt 3)).sub_const (Real.pi / 3) using 1 <;> first | rfl | ring
  exact hd.deriv

private theorem phi_cos_deriv (x : ℝ) : deriv (phiK .cos) x = 1 / 4 - Real.cos x ^ 2 := by
  have hd : HasDerivAt (phiK .cos) (1 / 4 - Real.cos x ^ 2) x := by
    convert ((hasDerivAt_const x (Real.pi / 12 + Real.sqrt 3 / 8)).sub ((hasDerivAt_id x).div_const 4)).sub ((((hasDerivAt_id x).const_mul 2).sin).div_const 4) using 1 <;> first | rfl | (simp only [Real.cos_two_mul, id_eq]; ring)
  exact hd.deriv

theorem proof_HardSphereB5_SphericalCrofton_rho_rational (f : Kern) (δ : ℝ) :
    deriv (phiK f) δ / (1 - Real.cos δ ^ 2) = rhoK f (Real.cos δ) := by
  cases f with
  | one => simp [phi_one_deriv, rhoK]
  | cos => simp [phi_cos_deriv, rhoK]

