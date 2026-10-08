import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_threshold
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_continuous
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_partial_branch
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_inner_integral
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_outer_branch
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_integral_threshold
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_arg_conversion
import HardSphereB5Lean.Theorems.Thm_SolidGeom_sliceCap_integral
import HardSphereB5Lean.Theorems.Thm_SolidGeom_sliceCap_integral_endpoint
set_option autoImplicit false
open MeasureTheory Real Set
set_option maxHeartbeats 1600000

theorem proof_SolidGeom_twoCapSlice_integral (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) :
    2 * (∫ z in (0 : ℝ)..min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)),
      max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
        (min (2 * arccos (l / sqrt (1 - z ^ 2)))
          (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha)))) =
      2 * π - 2 * Complex.arg ⟨cos alpha - k * l, sqrt (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)⟩ -
      2 * k * Complex.arg ⟨l - k * cos alpha, sqrt (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)⟩ -
      2 * l * Complex.arg ⟨k - l * cos alpha, sqrt (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)⟩ := by

  let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
  let h := sqrt D / sin alpha
  let Ck := sqrt (1 - k ^ 2)
  let Cl := sqrt (1 - l ^ 2)
  let H := min Ck Cl
  let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
  let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
  let e := fun z : ℝ => max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha)))
  let Xk := l - k * cos alpha
  let Xl := k - l * cos alpha
  let Tk := if Xk = 0 then π / 2 else arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2))
  let Tl := if Xl = 0 then π / 2 else arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2))
  change 2 * (∫ z in (0 : ℝ)..H, e z) =
    2 * π - 2 * Complex.arg ⟨cos alpha - k * l, sqrt D⟩ -
    2 * k * Complex.arg ⟨Xk, sqrt D⟩ - 2 * l * Complex.arg ⟨Xl, sqrt D⟩
  have hthreshold := SolidGeom.twoCapSlice_threshold k l alpha hk0 hk1 hl0 hl1 ha0 hap hD
  change 0 < h ∧ h ≤ H ∧
    1 - k ^ 2 - h ^ 2 = Xk ^ 2 / sin alpha ^ 2 ∧
    1 - l ^ 2 - h ^ 2 = Xl ^ 2 / sin alpha ^ 2 at hthreshold
  rcases hthreshold with ⟨hh, hhH, hradk, hradl⟩
  have hs : 0 < sin alpha := sin_pos_of_pos_of_lt_pi ha0 hap
  have hCk : 0 < 1 - k ^ 2 := by nlinarith [mul_pos hk0 (sub_pos.mpr hk1)]
  have hCl : 0 < 1 - l ^ 2 := by nlinarith [mul_pos hl0 (sub_pos.mpr hl1)]
  have hsCk : Ck ^ 2 = 1 - k ^ 2 := sq_sqrt hCk.le
  have hsCl : Cl ^ 2 = 1 - l ^ 2 := sq_sqrt hCl.le
  have hnCk : 0 ≤ Ck := sqrt_nonneg _
  have hnCl : 0 ≤ Cl := sqrt_nonneg _
  have hH0 : 0 ≤ H := hh.le.trans hhH
  have hhk : h ^ 2 ≤ 1 - k ^ 2 := by
    have hk := hhH.trans (min_le_left Ck Cl)
    nlinarith
  have hhl : h ^ 2 ≤ 1 - l ^ 2 := by
    have hl := hhH.trans (min_le_right Ck Cl)
    nlinarith
  have hh2 : h ^ 2 = D / sin alpha ^ 2 := by
    dsimp [h]
    rw [div_pow, sq_sqrt hD.le]
  have hD2 : D = sin alpha ^ 2 * h ^ 2 := by
    have := (eq_div_iff (ne_of_gt (sq_pos_of_pos hs))).mp hh2
    nlinarith [this]
  have hcont (a : ℝ) : ContinuousOn (fun z : ℝ => arccos (a / sqrt (1 - z ^ 2))) (Icc 0 H) := by
    intro z hz
    have hzCk : z ≤ Ck := hz.2.trans (min_le_left _ _)
    have hzsq : z ^ 2 ≤ 1 - k ^ 2 := by nlinarith [hz.1]
    have hroot : sqrt (1 - z ^ 2) ≠ 0 := sqrt_ne_zero'.mpr (by nlinarith [sq_pos_of_pos hk0])
    have hd : ContinuousAt (fun z : ℝ => sqrt (1 - z ^ 2)) z :=
      (continuousAt_const.sub (continuousAt_id.pow 2)).sqrt
    exact (continuous_arccos.continuousAt.comp (continuousAt_const.div hd hroot)).continuousWithinAt
  have hfcont : ContinuousOn f (Icc 0 H) := hcont k
  have hgcont : ContinuousOn g (Icc 0 H) := hcont l
  have hecont : ContinuousOn e (Icc 0 H) :=
    SolidGeom.twoCapSlice_continuous k l alpha hk0 hk1 hl0 hl1
  have hinterior : EqOn e (fun z => f z + g z - alpha) (Ico 0 h) := by
    intro z hz
    have hzsq : z ^ 2 < h ^ 2 := by nlinarith [hz.1, hz.2]
    have hzk : z ^ 2 < 1 - k ^ 2 := lt_of_lt_of_le hzsq hhk
    have hzl : z ^ 2 < 1 - l ^ 2 := lt_of_lt_of_le hzsq hhl
    have hDz : 0 < sin alpha ^ 2 * (1 - z ^ 2) - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha := by
      have hprod := mul_pos (sq_pos_of_pos hs) (sub_pos.mpr hzsq)
      dsimp [D] at hD2
      nlinarith
    exact SolidGeom.twoCapSlice_partial_branch k l alpha z hk0 hk1 hl0 hl1 ha0 hap hzk hzl hDz
  have hbclosed : EqOn e (fun z => f z + g z - alpha) (Icc 0 h) :=
    hinterior.of_subset_closure
      (hecont.mono (Icc_subset_Icc le_rfl hhH))
      (((hfcont.add hgcont).sub continuousOn_const).mono (Icc_subset_Icc le_rfl hhH))
      Ico_subset_Icc_self (by rw [closure_Ico hh.ne])
  have hbinner : e h = f h + g h - alpha := hbclosed ⟨hh.le, le_rfl⟩
  have houter (z : ℝ) (hz : h ≤ z) (hzH : z ≤ H) :
      e z = if l < k * cos alpha then 2 * f z else if k < l * cos alpha then 2 * g z else 0 :=
    SolidGeom.twoCapSlice_outer_branch k l alpha hk0 hk1 hl0 hl1 ha0 hap hD z hz hzH
  have hbouter := houter h le_rfl hhH
  have hIh : (∫ z in (0 : ℝ)..h, e z) =
      h * (f h + g h - alpha) + Tk + Tl - k * arcsin (h / Ck) - l * arcsin (h / Cl) :=
    SolidGeom.twoCapSlice_integral_threshold k l alpha hk0 hk1 hl0 hl1 ha0 hap hD
  have harg := SolidGeom.twoCapSlice_arg_conversion k l alpha hk0 hk1 hl0 hl1 ha0 hap hD
  change Complex.arg ⟨Xk, sqrt D⟩ = (if Xk < 0 then π - arcsin (h / Ck) else arcsin (h / Ck)) ∧
    Complex.arg ⟨Xl, sqrt D⟩ = (if Xl < 0 then π - arcsin (h / Cl) else arcsin (h / Cl)) ∧
    Complex.arg ⟨cos alpha - k * l, sqrt D⟩ =
      (if Xk < 0 then Tk - Tl else if Xl < 0 then Tl - Tk else π - Tk - Tl) at harg
  rw [harg.1, harg.2.1, harg.2.2]
  have he0h : IntervalIntegrable e volume 0 h :=
    (hecont.mono (Icc_subset_Icc le_rfl hhH)).intervalIntegrable_of_Icc hh.le
  have hehH : IntervalIntegrable e volume h H :=
    (hecont.mono (Icc_subset_Icc hh.le le_rfl)).intervalIntegrable_of_Icc hhH
  have hsplit := intervalIntegral.integral_add_adjacent_intervals he0h hehH
  by_cases hxk : l < k * cos alpha
  · have hlk : l < k := lt_of_lt_of_le hxk (by nlinarith [cos_le_one alpha])
    have hxl : ¬ k < l * cos alpha := by nlinarith [cos_le_one alpha]
    have hxkn : Xk < 0 := sub_neg.mpr hxk
    have hxln : ¬ Xl < 0 := by simpa only [Xl, sub_neg] using hxl
    have hxkne : Xk ≠ 0 := ne_of_lt hxkn
    have hH : H = Ck := min_eq_left (by nlinarith [mul_pos (sub_pos.mpr hlk) (add_pos hk0 hl0)])
    have hstrict : h ^ 2 < 1 - k ^ 2 := by
      have hpos : 0 < Xk ^ 2 / sin alpha ^ 2 := div_pos (sq_pos_of_ne_zero hxkne) (sq_pos_of_pos hs)
      linarith
    have hTk : Tk = arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2)) := by simp only [Tk, if_neg hxkne]
    have hfull : (∫ z in (0 : ℝ)..H, f z) = π * (1 - k) / 2 := by
      rw [hH]
      exact SolidGeom.sliceCap_integral_endpoint k hk0 hk1
    have hcap : (∫ z in (0 : ℝ)..h, f z) = h * f h + Tk - k * arcsin (h / Ck) := by
      rw [hTk]
      exact SolidGeom.sliceCap_integral k h hk0 hk1 hh.le hstrict
    have hf0H : IntervalIntegrable f volume 0 H := hfcont.intervalIntegrable_of_Icc hH0
    have hf0h : IntervalIntegrable f volume 0 h :=
      (hfcont.mono (Icc_subset_Icc le_rfl hhH)).intervalIntegrable_of_Icc hh.le
    have hout : (∫ z in h..H, e z) = 2 * ((∫ z in (0 : ℝ)..H, f z) - ∫ z in (0 : ℝ)..h, f z) := by
      calc
        _ = ∫ z in h..H, 2 * f z := intervalIntegral.integral_congr (by
          intro z hz
          rw [uIcc_of_le hhH] at hz
          simpa only [if_pos hxk] using houter z hz.1 hz.2)
        _ = 2 * (∫ z in h..H, f z) := intervalIntegral.integral_const_mul 2 f
        _ = _ := congrArg (fun r : ℝ => 2 * r) (intervalIntegral.integral_interval_sub_left hf0H hf0h).symm
    have hb : g h - f h - alpha = 0 := by
      simp only [if_pos hxk] at hbouter
      linarith [hbinner, hbouter]
    simp only [if_pos hxkn, if_neg hxln]
    rw [← hsplit, hIh, hout, hfull, hcap]
    linear_combination 2 * h * hb
  · by_cases hxl : k < l * cos alpha
    · have hkl : k < l := lt_of_lt_of_le hxl (by nlinarith [cos_le_one alpha])
      have hxkn : ¬ Xk < 0 := by simpa only [Xk, sub_neg] using hxk
      have hxln : Xl < 0 := sub_neg.mpr hxl
      have hxlne : Xl ≠ 0 := ne_of_lt hxln
      have hH : H = Cl := min_eq_right (by nlinarith [mul_pos (sub_pos.mpr hkl) (add_pos hk0 hl0)])
      have hstrict : h ^ 2 < 1 - l ^ 2 := by
        have hpos : 0 < Xl ^ 2 / sin alpha ^ 2 := div_pos (sq_pos_of_ne_zero hxlne) (sq_pos_of_pos hs)
        linarith
      have hTl : Tl = arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2)) := by simp only [Tl, if_neg hxlne]
      have hfull : (∫ z in (0 : ℝ)..H, g z) = π * (1 - l) / 2 := by
        rw [hH]
        exact SolidGeom.sliceCap_integral_endpoint l hl0 hl1
      have hcap : (∫ z in (0 : ℝ)..h, g z) = h * g h + Tl - l * arcsin (h / Cl) := by
        rw [hTl]
        exact SolidGeom.sliceCap_integral l h hl0 hl1 hh.le hstrict
      have hg0H : IntervalIntegrable g volume 0 H := hgcont.intervalIntegrable_of_Icc hH0
      have hg0h : IntervalIntegrable g volume 0 h :=
        (hgcont.mono (Icc_subset_Icc le_rfl hhH)).intervalIntegrable_of_Icc hh.le
      have hout : (∫ z in h..H, e z) = 2 * ((∫ z in (0 : ℝ)..H, g z) - ∫ z in (0 : ℝ)..h, g z) := by
        calc
          _ = ∫ z in h..H, 2 * g z := intervalIntegral.integral_congr (by
            intro z hz
            rw [uIcc_of_le hhH] at hz
            simpa only [if_neg hxk, if_pos hxl] using houter z hz.1 hz.2)
          _ = 2 * (∫ z in h..H, g z) := intervalIntegral.integral_const_mul 2 g
          _ = _ := congrArg (fun r : ℝ => 2 * r) (intervalIntegral.integral_interval_sub_left hg0H hg0h).symm
      have hb : f h - g h - alpha = 0 := by
        simp only [if_neg hxk, if_pos hxl] at hbouter
        linarith [hbinner, hbouter]
      simp only [if_neg hxkn, if_pos hxln]
      rw [← hsplit, hIh, hout, hfull, hcap]
      linear_combination 2 * h * hb
    · have hxkn : ¬ Xk < 0 := by simpa only [Xk, sub_neg] using hxk
      have hxln : ¬ Xl < 0 := by simpa only [Xl, sub_neg] using hxl
      have hout : (∫ z in h..H, e z) = 0 := by
        calc
          _ = ∫ z in h..H, (0 : ℝ) := intervalIntegral.integral_congr (by
            intro z hz
            rw [uIcc_of_le hhH] at hz
            simpa only [if_neg hxk, if_neg hxl] using houter z hz.1 hz.2)
          _ = 0 := by simp
      have hb : f h + g h - alpha = 0 := by
        simp only [if_neg hxk, if_neg hxl] at hbouter
        linarith [hbinner, hbouter]
      simp only [if_neg hxkn, if_neg hxln]
      rw [← hsplit, hIh, hout]
      linear_combination 2 * h * hb
