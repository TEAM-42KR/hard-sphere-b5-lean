import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_sq_lintegral : (∫⁻ r in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (r^2)) = (3:ENNReal)⁻¹ := by
  have hi : IntegrableOn (fun r : ℝ => r^2) (Set.Ioo 0 1) := by
    have hcc : IntegrableOn (fun r : ℝ => r^2) (Set.Icc 0 1) :=
      (continuous_id.pow 2).integrableOn_Icc
    exact hcc.mono_set Set.Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun r => sq_nonneg r)]
  have he : (∫ r in Set.Ioo (0:ℝ) 1, r^2) = (1/3:ℝ) := by
    rw [restrict_Ioo_eq_restrict_Icc, ← restrict_Ioc_eq_restrict_Icc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1), integral_pow]
    norm_num
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num
