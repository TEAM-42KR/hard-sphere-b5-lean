import Mathlib
set_option autoImplicit false
open MeasureTheory

set_option maxRecDepth 1000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_inverse_sqrt_height (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    IntervalIntegrable (fun t : ℝ => (r * r + 1 - 2 * r * t) ^ (-1 / 2 : ℝ))
      volume (-1) 1 ∧
    (∫ t in (-1 : ℝ)..1, (r * r + 1 - 2 * r * t) ^ (-1 / 2 : ℝ)) = 2 := by
  have hc : -2 * r ≠ 0 := mul_ne_zero (by norm_num) hr.ne'
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ (-1 / 2 : ℝ)) volume
      (-2 * r * (-1) + (r * r + 1)) (-2 * r * 1 + (r * r + 1)) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hi := (hpow.comp_add_right (r * r + 1)).comp_mul_left (c := -2 * r)
  have hA : (-2 * r * (-1) + (r * r + 1) - (r * r + 1)) / (-2 * r) = -1 := by
    field_simp
    <;> ring
  have hB : (-2 * r * 1 + (r * r + 1) - (r * r + 1)) / (-2 * r) = 1 := by
    field_simp
    <;> ring
  rw [hA, hB] at hi
  have hf : (fun t : ℝ => (-2 * r * t + (r * r + 1)) ^ (-1 / 2 : ℝ)) =
      (fun t : ℝ => (r * r + 1 - 2 * r * t) ^ (-1 / 2 : ℝ)) := by
    funext t
    congr 1
    ring
  rw [hf] at hi
  refine ⟨hi, ?_⟩
  have hchange := intervalIntegral.mul_integral_comp_mul_add
    (f := fun u : ℝ => u ^ (-1 / 2 : ℝ)) (a := (-1 : ℝ)) (b := 1)
    (-2 * r) (r * r + 1)
  rw [hf] at hchange
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))] at hchange
  have hp : -2 * r * (-1) + (r * r + 1) = (1 + r) ^ 2 := by ring
  have hm : -2 * r * 1 + (r * r + 1) = (1 - r) ^ 2 := by ring
  have hep : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hp, hm, hep, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hchange
  rw [Real.sqrt_sq (by linarith : 0 ≤ 1 + r), Real.sqrt_sq (by linarith : 0 ≤ 1 - r)] at hchange
  nlinarith
