import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem proof_SphereGeom_polar_cosine_substitution (f : ℝ → ℝ) :
 (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * f (Real.cos θ)) =
 ∫ z in (-1 : ℝ)..1, f z := by
  have H := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos) (f' := fun θ => -Real.sin θ) (g := f)
    Real.continuous_cos.continuousOn
    (fun θ _ => Real.hasDerivAt_cos θ)
    (fun θ hθ => by
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc
        ⟨by simpa [Real.pi_pos.le] using hθ.1.le, by simpa [Real.pi_pos.le] using hθ.2.le⟩
      linarith)
  have H' : -(∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * f (Real.cos θ)) =
      ∫ z in (1 : ℝ)..(-1), f z := by
    simpa only [Function.comp_apply, mul_neg, neg_mul, mul_comm, intervalIntegral.integral_neg,
      Real.cos_zero, Real.cos_pi] using H
  have hr : (∫ z in (1 : ℝ)..(-1), f z) = -(∫ z in (-1 : ℝ)..1, f z) :=
    intervalIntegral.integral_symm _ _
  rw [hr] at H'
  exact neg_injective H'
