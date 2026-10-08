import HardSphereB5Lean.Theorems.Thm_SphereGeom_twoCap_area_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_indicator_integrable
import HardSphereB5Lean.Theorems.Thm_SphereGeom_polar_cosine_substitution
import HardSphereB5Lean.Theorems.Thm_SphereGeom_twoCap_polar_azimuth_slice
set_option autoImplicit false

open SphereGeom MeasureTheory Real Set
set_option maxHeartbeats 1000000

theorem proof_SphereGeom_twoCap_area_slice (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (k l alpha : ℝ) (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (ha1 : alpha < Real.pi) :
    let H := min (Real.sqrt (1 - k ^ 2)) (Real.sqrt (1 - l ^ 2))
    let f := fun z : ℝ => Real.arccos (k / Real.sqrt (1 - z ^ 2))
    let g := fun z : ℝ => Real.arccos (l / Real.sqrt (1 - z ^ 2))
    (dOmega (cap (e 0) k ∩ cap (Real.cos alpha • e 0 + Real.sin alpha • e 1) l)).toReal =
      2 * (∫ z in (0 : ℝ)..H, max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha)))) := by
  let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
  let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
  let L := fun z : ℝ => max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha)))
  let H := min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2))
  change (dOmega (cap (e 0) k ∩ cap (cos alpha • e 0 + sin alpha • e 1) l)).toReal =
    2 * (∫ z in (0 : ℝ)..H, L z)
  have hqC (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : 0 < 1 - q ^ 2 := by
    have hs := (sq_lt_sq₀ hq0.le (by norm_num : (0 : ℝ) ≤ 1)).2 hq1
    nlinarith
  have hkC := hqC k hk0 hk1
  have hlC := hqC l hl0 hl1
  have hH0 : 0 < H := lt_min (sqrt_pos.2 hkC) (sqrt_pos.2 hlC)
  have hsk1 : sqrt (1 - k ^ 2) < 1 := by
    have hs := sq_sqrt hkC.le
    have hn := sqrt_nonneg (1 - k ^ 2)
    nlinarith [sq_pos_of_pos hk0]
  have hH1 : H < 1 := lt_of_le_of_lt (min_le_left _ _) hsk1
  have hLnonneg (z : ℝ) : 0 ≤ L z := le_max_left _ _
  have hLbound (z : ℝ) : L z ≤ 2 * π := by
    apply max_le (by linarith [pi_pos])
    exact (min_le_left _ _).trans (by
      dsimp [f]
      linarith [arccos_le_pi (k / sqrt (1 - z ^ 2))])
  have hLm : Measurable L := by dsimp [L, f, g]; fun_prop
  have hint (a b : ℝ) : IntervalIntegrable L volume a b := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 * π) volume a b).mono_fun'
      hLm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (hLnonneg z)]
      exact hLbound z)
  have heven (z : ℝ) : L (-z) = L z := by simp only [L, f, g, neg_sq]
  have hLzero (z : ℝ) (hz : z ∈ Ioo H 1) : L z = 0 := by
    have hz0 : 0 < z := lt_trans hH0 hz.1
    have hzsq : z ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hz.2) (add_pos (by norm_num : (0 : ℝ) < 1) hz0)]
    have hrad : 0 < 1 - z ^ 2 := by linarith
    have hrp : 0 < sqrt (1 - z ^ 2) := sqrt_pos.2 hrad
    have hsq : sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := sq_sqrt hrad.le
    have hzero (q : ℝ) (hq0 : 0 < q) (hqC : 0 < 1 - q ^ 2)
        (hqz : sqrt (1 - q ^ 2) < z) : arccos (q / sqrt (1 - z ^ 2)) = 0 := by
      have hc := sq_sqrt hqC.le
      have hcn := sqrt_nonneg (1 - q ^ 2)
      have hzs : 1 - q ^ 2 < z ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr hqz) (add_pos_of_pos_of_nonneg hz0 hcn)]
      have hlt : sqrt (1 - z ^ 2) < q := by nlinarith
      apply arccos_eq_zero.mpr
      exact (le_div_iff₀ hrp).2 (by simpa using hlt.le)
    have hmin : sqrt (1 - k ^ 2) < z ∨ sqrt (1 - l ^ 2) < z := min_lt_iff.mp hz.1
    rcases hmin with hkz | hlz
    · have hf0 : f z = 0 := hzero k hk0 hkC hkz
      change max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha))) = 0
      rw [hf0, mul_zero]
      exact max_eq_left (min_le_left _ _)
    · have hg0 : g z = 0 := hzero l hl0 hlC hlz
      change max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha))) = 0
      rw [hg0, mul_zero]
      exact max_eq_left ((min_le_right _ _).trans (min_le_left _ _))
  have htail : (∫ z in H..(1 : ℝ), L z) = 0 := by
    calc
      (∫ z in H..(1 : ℝ), L z) = ∫ z in H..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro z hz
        exact hLzero z (by simpa only [uIoo_of_le hH1.le] using hz)
      _ = 0 := intervalIntegral.integral_zero
  have htruncate : (∫ z in (0 : ℝ)..1, L z) = ∫ z in (0 : ℝ)..H, L z := by
    have ht := intervalIntegral.integral_add_adjacent_intervals (hint 0 H) (hint H 1)
    simpa only [htail, add_zero] using ht.symm
  have hnegative : (∫ z in (-1 : ℝ)..0, L z) = ∫ z in (0 : ℝ)..1, L z := by
    have ht := intervalIntegral.integral_comp_neg (f := L) (a := (0 : ℝ)) (b := 1)
    simpa only [heven, neg_zero] using ht.symm
  have hcap (v : E3) (q : ℝ) : MeasurableSet (cap v q) := by
    unfold cap
    exact (isClosed_eq (by fun_prop : Continuous (fun u : E3 => ‖u‖)) continuous_const).measurableSet.inter
      (isClosed_le continuous_const (by fun_prop : Continuous (fun u : E3 => inner ℝ v u))).measurableSet
  have hArea := SphereGeom.twoCap_area_frame e he (e 0) (cos alpha • e 0 + sin alpha • e 1) k l
    (SphereGeom.dOmega_indicator_integrable _ ((hcap _ _).inter (hcap _ _)))
  calc
    (dOmega (cap (e 0) k ∩ cap (cos alpha • e 0 + sin alpha • e 1) l)).toReal =
        ∫ theta in (0 : ℝ)..π, sin theta * L (cos theta) := by
      rw [hArea]
      apply intervalIntegral.integral_congr_uIoo
      intro theta ht
      dsimp only
      have hth : theta ∈ Ioo (0 : ℝ) π := by simpa only [uIoo_of_le pi_pos.le] using ht
      rw [intervalIntegral.integral_const_mul]
      congr 1
      exact SphereGeom.twoCap_polar_azimuth_slice e he k l alpha theta hk0 hl0 ha0.le ha1.le hth.1 hth.2
    _ = ∫ z in (-1 : ℝ)..1, L z := SphereGeom.polar_cosine_substitution L
    _ = 2 * (∫ z in (0 : ℝ)..H, L z) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-1) 0) (hint 0 1),
        hnegative, htruncate]
      ring
