import Mathlib
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem proof_SphereGeom_Aux_SphericalCoordinates_cosHeightMeasure :
    ((volume.restrict (Set.Ioc (0 : ℝ) Real.pi)).withDensity
      (fun θ => ENNReal.ofReal (Real.sin θ))).map Real.cos =
    volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  have hw : Measurable (fun θ => ENNReal.ofReal (Real.sin θ)) := by fun_prop
  have himage : Real.cos '' Set.Icc (0 : ℝ) Real.pi = Set.Icc (-1 : ℝ) 1 :=
    Real.cosPartialEquiv.image_source_eq_target
  have hderiv (x : ℝ) (_hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
      HasDerivWithinAt Real.cos (-Real.sin x) (Set.Icc (0 : ℝ) Real.pi) x :=
    (Real.hasDerivAt_cos x).hasDerivWithinAt
  have hrestrict : (volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi) =
      volume.restrict (Set.Icc 0 Real.pi) := restrict_Ioc_eq_restrict_Icc
  rw [hrestrict]
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg Real.measurable_cos]
  rw [lintegral_withDensity_eq_lintegral_mul _ hw
    (show Measurable (fun x => g (Real.cos x)) from hg.comp Real.measurable_cos)]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv
    Real.injOn_cos g
  rw [himage] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only [Pi.mul_apply]
  rw [abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)]
