import Mathlib
set_option autoImplicit false
open MeasureTheory Real
noncomputable section
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_even_overlap (h : ℝ → ENNReal) (he : ∀ r, h (-r) = h r) (L : ℝ) (hL : 0 ≤ L) : (∫⁻ r, h r * ENNReal.ofReal (min L (L - r) - max 0 (-r))) = 2 * ∫⁻ r in Set.Ioc 0 L, h r * ENNReal.ofReal (L - r) := by
  let H : ℝ → ENNReal := fun r => h r * ENNReal.ofReal (min L (L - r) - max 0 (-r))
  have hp (r : ℝ) (hr : 0 ≤ r) : H r = h r * ENNReal.ofReal (L - r) := by
    simp [H, min_eq_right (by linarith : L - r ≤ L), max_eq_left (by linarith : -r ≤ 0)]
  have hn (r : ℝ) (hr : 0 ≤ r) : H (-r) = H r := by
    rw [hp r hr]
    simp [H, he, min_eq_left (by linarith : L ≤ L + r), max_eq_right hr]
  have hH (r : ℝ) : H (-r) = H r := by
    by_cases hr : 0 ≤ r
    · exact hn r hr
    · have hh := hn (-r) (by linarith : 0 ≤ -r)
      simpa using hh.symm
  have href : (∫⁻ r in Set.Iic 0, H r) = ∫⁻ r in Set.Ici 0, H r := by
    rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Ici]
    rw [← lintegral_neg_eq_self (μ := (volume : Measure ℝ))
      (fun r => (Set.Iic (0 : ℝ)).indicator H r)]
    apply lintegral_congr
    intro r
    simp [Set.indicator, hH]
  have hni : (∫⁻ r in Set.Iic 0, H r) = ∫⁻ r in Set.Ioi 0, H r := by
    rw [href]
    exact setLIntegral_congr (Ioi_ae_eq_Ici (μ := (volume : Measure ℝ)) (a := 0)).symm
  have hpi : (∫⁻ r in Set.Ioi 0, H r) =
      ∫⁻ r in Set.Ioc 0 L, h r * ENNReal.ofReal (L - r) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro r
    by_cases hr : 0 < r
    · by_cases hl : r ≤ L
      · simp [Set.indicator, hr, hl, hp r hr.le]
      · have hz : ENNReal.ofReal (L - r) = 0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
        simp [Set.indicator, hr, hl, hp r hr.le, hz]
    · simp [Set.indicator, hr]
  change (∫⁻ r, H r) = _
  rw [← lintegral_add_compl H measurableSet_Ioi, Set.compl_Ioi, hni, hpi]
  exact (two_mul _).symm
