import Mathlib
set_option autoImplicit false
open MeasureTheory Real
set_option maxHeartbeats 800000

theorem proof_SolidGeom_twoCapSlice_threshold (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) :
    let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
    let h := sqrt D / sin alpha
    0 < h ∧ h ≤ min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)) ∧
      1 - k ^ 2 - h ^ 2 = (l - k * cos alpha) ^ 2 / sin alpha ^ 2 ∧
      1 - l ^ 2 - h ^ 2 = (k - l * cos alpha) ^ 2 / sin alpha ^ 2 := by
  dsimp only
  let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
  let h := sqrt D / sin alpha
  change 0 < h ∧ h ≤ min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)) ∧
    1 - k ^ 2 - h ^ 2 = (l - k * cos alpha) ^ 2 / sin alpha ^ 2 ∧
    1 - l ^ 2 - h ^ 2 = (k - l * cos alpha) ^ 2 / sin alpha ^ 2
  have hs : 0 < sin alpha := sin_pos_of_pos_of_lt_pi ha0 hap
  have hh : 0 < h := div_pos (sqrt_pos.mpr hD) hs
  have hhsq : h ^ 2 = D / sin alpha ^ 2 := by
    dsimp [h]
    rw [div_pow, sq_sqrt hD.le]
  have hcircle := sin_sq_add_cos_sq alpha
  have hradk : 1 - k ^ 2 - h ^ 2 = (l - k * cos alpha) ^ 2 / sin alpha ^ 2 := by
    rw [hhsq]
    dsimp [D]
    field_simp [ne_of_gt hs]
    linear_combination -(k ^ 2) * hcircle
  have hradl : 1 - l ^ 2 - h ^ 2 = (k - l * cos alpha) ^ 2 / sin alpha ^ 2 := by
    rw [hhsq]
    dsimp [D]
    field_simp [ne_of_gt hs]
    linear_combination -(l ^ 2) * hcircle
  have hCk : 0 < 1 - k ^ 2 := by nlinarith [mul_pos hk0 (sub_pos.mpr hk1)]
  have hCl : 0 < 1 - l ^ 2 := by nlinarith [mul_pos hl0 (sub_pos.mpr hl1)]
  have hk2 : h ^ 2 ≤ 1 - k ^ 2 := by
    have hn : 0 ≤ (l - k * cos alpha) ^ 2 / sin alpha ^ 2 := by positivity
    linarith [hradk]
  have hl2 : h ^ 2 ≤ 1 - l ^ 2 := by
    have hn : 0 ≤ (k - l * cos alpha) ^ 2 / sin alpha ^ 2 := by positivity
    linarith [hradl]
  refine ⟨hh, le_min ?_ ?_, hradk, hradl⟩
  · nlinarith [sq_sqrt hCk.le, sqrt_nonneg (1 - k ^ 2)]
  · nlinarith [sq_sqrt hCl.le, sqrt_nonneg (1 - l ^ 2)]
