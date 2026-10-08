import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem int_one (d : ℝ) : (∫ t in (0 : ℝ)..d, wK .one (Real.cos t) * Real.sin t) = 1 - Real.cos d := by
  simp [wK, integral_sin]

private theorem int_cos (d : ℝ) : (∫ t in (0 : ℝ)..d, wK .cos (Real.cos t) * Real.sin t) = (1 - Real.cos d ^ 2) / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -(Real.cos t ^ 2) / 2) (wK .cos (Real.cos x) * Real.sin x) x := by
    intro x
    convert (((Real.hasDerivAt_cos x).pow 2).neg).div_const 2 using 1 <;> first | rfl | (simp only [wK]; ring)
  have hc : Continuous (fun t : ℝ => wK .cos (Real.cos t) * Real.sin t) := by unfold wK; fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x (_ : x ∈ Set.uIcc 0 d) => hd x) (hc.intervalIntegrable 0 d)
  simp only [Real.cos_zero] at hh
  convert hh using 1 <;> ring

private theorem int_t_one (d : ℝ) : (∫ t in (0 : ℝ)..d, t * wK .one (Real.cos t) * Real.sin t) = Real.sin d - d * Real.cos d := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.sin t - t * Real.cos t) (x * wK .one (Real.cos x) * Real.sin x) x := by
    intro x
    convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;> first | rfl | (simp only [wK, id_eq]; ring)
  have hc : Continuous (fun t : ℝ => t * wK .one (Real.cos t) * Real.sin t) := by unfold wK; fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x (_ : x ∈ Set.uIcc 0 d) => hd x) (hc.intervalIntegrable 0 d)
  simpa using hh

private theorem int_t_cos (d : ℝ) : (∫ t in (0 : ℝ)..d, t * wK .cos (Real.cos t) * Real.sin t) = Real.sin (2 * d) / 8 - d * Real.cos (2 * d) / 4 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.sin (2 * t) / 8 - t * Real.cos (2 * t) / 4) (x * wK .cos (Real.cos x) * Real.sin x) x := by
    intro x
    convert ((((hasDerivAt_id x).const_mul 2).sin).div_const 8).sub (((hasDerivAt_id x).mul (((hasDerivAt_id x).const_mul 2).cos)).div_const 4) using 1 <;> first | rfl | (simp only [wK, id_eq, Real.sin_two_mul]; ring)
  have hc : Continuous (fun t : ℝ => t * wK .cos (Real.cos t) * Real.sin t) := by unfold wK; fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x (_ : x ∈ Set.uIcc 0 d) => hd x) (hc.intervalIntegrable 0 d)
  simpa using hh

theorem proof_HardSphereB5_SphericalCrofton_kernel_constants :
    alphaK .one = 1 ∧ bK .one = √3 - π / 3 ∧ alphaK .cos = 3 / 4 ∧ bK .cos = √3 / 8 + π / 12 ∧
      (∀ f, cA f = π * alphaK f ∧ cP f = bK f) := by
  have ha1 : alphaK .one = 1 := by
    rw [alphaK, int_one, Real.cos_pi_div_three]; norm_num
  have hb1 : bK .one = √3 - π / 3 := by
    rw [bK, int_t_one, Real.sin_pi_div_three, Real.cos_pi_div_three]; ring
  have hac : alphaK .cos = 3 / 4 := by
    rw [alphaK, int_cos, Real.cos_pi_div_three]; norm_num
  have hbc : bK .cos = √3 / 8 + π / 12 := by
    rw [bK, int_t_cos, Real.sin_two_mul, Real.cos_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]; ring
  refine ⟨ha1, hb1, hac, hbc, ?_⟩
  intro f
  cases f <;> simp [cA, cP, ha1, hb1, hac, hbc] <;> ring

