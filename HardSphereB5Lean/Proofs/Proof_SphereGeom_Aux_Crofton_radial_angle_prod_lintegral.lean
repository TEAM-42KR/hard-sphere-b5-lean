import Mathlib
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_angle_abs_lintegral_Ioo
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_radial_sq_lintegral_Ioo
set_option autoImplicit false

open MeasureTheory

theorem proof_SphereGeom_Aux_Crofton_radial_angle_prod_lintegral (A B : ℝ) :
    (∫⁻ q : ℝ × ℝ in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (q.1 ^ 2 * |A * Real.cos q.2 + B * Real.sin q.2|)
        ∂(volume.prod volume)) =
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.sqrt (A ^ 2 + B ^ 2)) := by
  rw [← Measure.prod_restrict]
  calc
    _ = ∫⁻ q : ℝ × ℝ,
        ENNReal.ofReal (q.1 ^ 2) * ENNReal.ofReal |A * Real.cos q.2 + B * Real.sin q.2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
      apply lintegral_congr
      intro q
      exact ENNReal.ofReal_mul (sq_nonneg q.1)
    _ = (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 2)) *
        (∫⁻ ψ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal |A * Real.cos ψ + B * Real.sin ψ|) :=
      lintegral_prod_mul
        (f := fun r : ℝ => ENNReal.ofReal (r ^ 2))
        (g := fun ψ : ℝ => ENNReal.ofReal |A * Real.cos ψ + B * Real.sin ψ|)
        (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
        (ν := volume.restrict (Set.Ioo (0 : ℝ) (2 * Real.pi)))
        (by fun_prop) (by fun_prop)
    _ = ENNReal.ofReal (1 / 3 : ℝ) *
        ENNReal.ofReal (4 * Real.sqrt (A ^ 2 + B ^ 2)) := by
      rw [SphereGeom.Aux.Crofton.radial_sq_lintegral_Ioo,
        SphereGeom.Aux.Crofton.angle_abs_lintegral_Ioo]
    _ = ENNReal.ofReal ((4 / 3 : ℝ) * Real.sqrt (A ^ 2 + B ^ 2)) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      congr 1
      ring
