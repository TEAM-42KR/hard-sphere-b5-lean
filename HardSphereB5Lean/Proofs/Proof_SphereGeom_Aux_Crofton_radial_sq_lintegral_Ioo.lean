import Mathlib
set_option autoImplicit false

open MeasureTheory

theorem proof_SphereGeom_Aux_Crofton_radial_sq_lintegral_Ioo :
    (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 2)) =
      ENNReal.ofReal (1 / 3 : ℝ) := by
  have hc : Continuous (fun r : ℝ => r ^ 2) := by fun_prop
  have hi : IntegrableOn (fun r : ℝ => r ^ 2) (Set.Ioo (0 : ℝ) 1) :=
    (hc.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg x)]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  norm_num [integral_pow]
