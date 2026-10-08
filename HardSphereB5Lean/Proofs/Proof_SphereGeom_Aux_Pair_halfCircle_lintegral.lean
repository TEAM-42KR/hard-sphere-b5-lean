import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SphericalCoordinates_cosHeightMeasure
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_Aux_Pair_halfCircle_lintegral (u k : E3) (f : E3 → ENNReal) (hf : Measurable f) :
    (∫⁻ w in Set.Icc (-1 : ℝ) 1, f (w • u + Real.sqrt (1-w^2) • k)) =
    ∫⁻ s in Set.Ioc 0 Real.pi, ENNReal.ofReal (Real.sin s) * f (Real.cos s • u + Real.sin s • k) := by
  let h : ℝ → ENNReal := fun w => f (w • u + Real.sqrt (1-w^2) • k)
  have hh : Measurable h := hf.comp (by fun_prop)
  rw [← SphereGeom.Aux.SphericalCoordinates.cosHeightMeasure,
    lintegral_map hh Real.continuous_cos.measurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun s : ℝ => h (Real.cos s)) from hh.comp Real.continuous_cos.measurable)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have heq : 1-Real.cos s^2 = Real.sin s^2 := by nlinarith [Real.sin_sq_add_cos_sq s]
  have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le hs.2
  simp only [Pi.mul_apply,h,heq,Real.sqrt_sq hsin]
