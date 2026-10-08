import Mathlib
set_option autoImplicit false
open MeasureTheory Real
set_option maxHeartbeats 800000

theorem proof_SolidGeom_twoCapSlice_continuous (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1) :
    ContinuousOn (fun z : ℝ => max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
        (min (2 * arccos (l / sqrt (1 - z ^ 2)))
          (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha))))
      (Set.Icc (0 : ℝ) (min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)))) := by
  intro x hx
  have hCk : 0 < 1 - k ^ 2 := by nlinarith [mul_pos hk0 (sub_pos.mpr hk1)]
  have hxle : x ≤ sqrt (1 - k ^ 2) := hx.2.trans (min_le_left _ _)
  have hx2 : x ^ 2 ≤ 1 - k ^ 2 := by
    nlinarith [sq_sqrt hCk.le, sqrt_nonneg (1 - k ^ 2), hx.1]
  have hroot : sqrt (1 - x ^ 2) ≠ 0 := sqrt_ne_zero'.mpr (by
    nlinarith [sq_pos_of_pos hk0])
  have hd : ContinuousAt (fun z : ℝ => sqrt (1 - z ^ 2)) x :=
    (continuousAt_const.sub (continuousAt_id.pow 2)).sqrt
  have hfk : ContinuousAt (fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))) x :=
    continuous_arccos.continuousAt.comp (continuousAt_const.div hd hroot)
  have hfl : ContinuousAt (fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))) x :=
    continuous_arccos.continuousAt.comp (continuousAt_const.div hd hroot)
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_const.max ((continuousAt_const.mul hfk).min
    ((continuousAt_const.mul hfl).min ((hfk.add hfl).sub continuousAt_const)))
