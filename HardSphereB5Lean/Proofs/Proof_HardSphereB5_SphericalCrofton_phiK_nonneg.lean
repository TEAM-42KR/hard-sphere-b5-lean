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

theorem proof_HardSphereB5_SphericalCrofton_phiK_nonneg (f : Kern) (L : ℝ) (h0 : 0 ≤ L) (h1 : L ≤ π / 3) : 0 ≤ phiK f L := by
  have hπ3 : (0 : ℝ) ≤ π / 3 := by positivity
  have hπ3π : π / 3 ≤ π := by linarith [Real.pi_pos]
  have hdiff : Differentiable ℝ (phiK f) := by cases f <;> unfold phiK <;> fun_prop
  have hanti : AntitoneOn (phiK f) (Set.Icc 0 (π / 3)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (π / 3)) hdiff.continuous.continuousOn hdiff.differentiableOn
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (π / 3) := interior_subset hx
    have hcos : (1 / 2 : ℝ) ≤ Real.cos x := by
      simpa only [Real.cos_pi_div_three] using Real.cos_le_cos_of_nonneg_of_le_pi hx'.1 hπ3π hx'.2
    cases f with
    | one => rw [phi_one_deriv]; linarith
    | cos => rw [phi_cos_deriv]; nlinarith
  have hzero : phiK f (π / 3) = 0 := by
    cases f <;> simp [phiK, Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three] <;> ring
  have hh := hanti ⟨h0, h1⟩ ⟨hπ3, le_rfl⟩ h1
  rwa [hzero] at hh

