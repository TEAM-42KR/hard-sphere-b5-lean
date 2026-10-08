import Mathlib
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_angle_abs_integral
set_option autoImplicit false

open MeasureTheory

theorem proof_SphereGeom_Aux_Crofton_angle_abs_lintegral_Ioo (A B : ℝ) :
    (∫⁻ ψ in Set.Ioo (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal |A * Real.cos ψ + B * Real.sin ψ|) =
        ENNReal.ofReal (4 * Real.sqrt (A ^ 2 + B ^ 2)) := by
  have hc : Continuous (fun ψ : ℝ => |A * Real.cos ψ + B * Real.sin ψ|) := by
    fun_prop
  have hi : IntegrableOn (fun ψ : ℝ => |A * Real.cos ψ + B * Real.sin ψ|)
      (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
    (hc.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => abs_nonneg _)]
  have h := SphereGeom.Aux.Crofton.angle_abs_integral A B
  rw [intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo] at h
  rw [h]
