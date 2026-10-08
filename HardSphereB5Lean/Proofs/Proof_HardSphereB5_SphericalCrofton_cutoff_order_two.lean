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

theorem proof_HardSphereB5_SphericalCrofton_cutoff_order_two (f : Kern) :
    phiK f (π / 3) = 0 ∧ deriv (phiK f) (π / 3) = 0 ∧
      ∀ L, deriv (deriv (phiK f)) L = 2 * wK f (Real.cos L) * Real.sin L := by
  cases f with
  | one =>
    refine ⟨?_, ?_, ?_⟩
    · simp [phiK, Real.sin_pi_div_three]; ring
    · rw [phi_one_deriv, Real.cos_pi_div_three]; norm_num
    · intro L
      rw [show deriv (phiK .one) = (fun x => 1 - 2 * Real.cos x) from funext phi_one_deriv]
      have hd := (hasDerivAt_const L (1 : ℝ)).sub ((Real.hasDerivAt_cos L).const_mul 2)
      convert hd.deriv using 1 <;> first | rfl | (simp only [wK]; ring)
  | cos =>
    refine ⟨?_, ?_, ?_⟩
    · simp [phiK, Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]; ring
    · rw [phi_cos_deriv, Real.cos_pi_div_three]; norm_num
    · intro L
      rw [show deriv (phiK .cos) = (fun x => 1 / 4 - Real.cos x ^ 2) from funext phi_cos_deriv]
      have hd := (hasDerivAt_const L (1 / 4 : ℝ)).sub ((Real.hasDerivAt_cos L).pow 2)
      convert hd.deriv using 1 <;> first | rfl | (simp only [wK]; ring)

