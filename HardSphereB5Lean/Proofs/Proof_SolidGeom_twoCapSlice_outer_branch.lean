import Mathlib
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_threshold
set_option autoImplicit false
open MeasureTheory Real
set_option maxHeartbeats 1600000

theorem proof_SolidGeom_twoCapSlice_outer_branch (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) (z : ℝ) :
    let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
    let h := sqrt D / sin alpha
    let Ck := sqrt (1 - k ^ 2)
    let Cl := sqrt (1 - l ^ 2)
    let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
    let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
    h ≤ z → z ≤ min Ck Cl →
      max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha))) =
        if l < k * cos alpha then 2 * f z
        else if k < l * cos alpha then 2 * g z else 0 := by
  dsimp only
  let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
  let h := sqrt D / sin alpha
  let A := 1 - z ^ 2
  let r := sqrt A
  let b := sqrt (A - k ^ 2)
  let d := sqrt (A - l ^ 2)
  let f := arccos (k / r)
  let g := arccos (l / r)
  change h ≤ z → z ≤ min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)) →
    max 0 (min (2 * f) (min (2 * g) (f + g - alpha))) =
      if l < k * cos alpha then 2 * f else if k < l * cos alpha then 2 * g else 0
  intro hz hH
  have hs : 0 < sin alpha := sin_pos_of_pos_of_lt_pi ha0 hap
  have hthreshold := SolidGeom.twoCapSlice_threshold k l alpha hk0 hk1 hl0 hl1 ha0 hap hD
  have hh : 0 < h := hthreshold.1
  have hz0 : 0 ≤ z := le_trans hh.le hz
  have hCk : 0 < 1 - k ^ 2 := by nlinarith only [hk0, hk1, mul_pos hk0 (sub_pos.mpr hk1)]
  have hCl : 0 < 1 - l ^ 2 := by nlinarith only [hl0, hl1, mul_pos hl0 (sub_pos.mpr hl1)]
  have hzk : z ^ 2 ≤ 1 - k ^ 2 := by
    have hzC := hH.trans (min_le_left _ _)
    nlinarith only [hz0, hzC, sq_sqrt hCk.le, sqrt_nonneg (1 - k ^ 2)]
  have hzl : z ^ 2 ≤ 1 - l ^ 2 := by
    have hzC := hH.trans (min_le_right _ _)
    nlinarith only [hz0, hzC, sq_sqrt hCl.le, sqrt_nonneg (1 - l ^ 2)]
  have hAk : 0 ≤ A - k ^ 2 := by dsimp [A]; linarith only [hzk]
  have hAl : 0 ≤ A - l ^ 2 := by dsimp [A]; linarith only [hzl]
  have hA : 0 < A := by nlinarith only [hAk, sq_pos_of_pos hk0]
  have hr : 0 < r := sqrt_pos.mpr hA
  have hr2 : r ^ 2 = A := sq_sqrt hA.le
  have hb : 0 ≤ b := sqrt_nonneg _
  have hd : 0 ≤ d := sqrt_nonneg _
  have hb2 : b ^ 2 = A - k ^ 2 := sq_sqrt hAk
  have hd2 : d ^ 2 = A - l ^ 2 := sq_sqrt hAl
  have hkr : 0 < k / r := div_pos hk0 hr
  have hlr : 0 < l / r := div_pos hl0 hr
  have hkr1 : k / r ≤ 1 := (div_le_one hr).mpr (by nlinarith only [hr2, hAk, hk0, hr])
  have hlr1 : l / r ≤ 1 := (div_le_one hr).mpr (by nlinarith only [hr2, hAl, hl0, hr])
  have hf0 : 0 ≤ f := arccos_nonneg _
  have hg0 : 0 ≤ g := arccos_nonneg _
  have hfp : f < π / 2 := arccos_lt_pi_div_two.mpr hkr
  have hgp : g < π / 2 := arccos_lt_pi_div_two.mpr hlr
  have hcf : cos f = k / r := cos_arccos (by linarith only [hkr]) hkr1
  have hcg : cos g = l / r := cos_arccos (by linarith only [hlr]) hlr1
  have hsf : sin f = b / r := by
    dsimp only [f]
    rw [sin_arccos]
    have he : 1 - (k / r) ^ 2 = (A - k ^ 2) / A := by
      rw [div_pow, hr2]
      field_simp [ne_of_gt hA] <;> ring
    rw [he, sqrt_div hAk]
  have hsg : sin g = d / r := by
    dsimp only [g]
    rw [sin_arccos]
    have he : 1 - (l / r) ^ 2 = (A - l ^ 2) / A := by
      rw [div_pow, hr2]
      field_simp [ne_of_gt hA] <;> ring
    rw [he, sqrt_div hAl]
  let P := b * d
  let X := A * cos alpha - k * l
  have hP : 0 ≤ P := mul_nonneg hb hd
  have hpluscos : cos (f + g) = (k * l - P) / A := by
    rw [cos_add, hcf, hcg, hsf, hsg]
    dsimp only [P]
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← pow_two, hr2]
  have hminuscos : cos (f - g) = (k * l + P) / A := by
    rw [cos_sub, hcf, hcg, hsf, hsg]
    dsimp only [P]
    rw [div_mul_div_comm, div_mul_div_comm, ← add_div, ← pow_two, hr2]
  have hhsq : h ^ 2 * sin alpha ^ 2 = D := by
    dsimp only [h]
    rw [div_pow, sq_sqrt hD.le]
    field_simp [ne_of_gt hs] <;> dsimp only [D] <;> ring
  have hzhsq : h ^ 2 ≤ z ^ 2 := (sq_le_sq₀ hh.le hz0).mpr hz
  have hmul : D ≤ sin alpha ^ 2 * z ^ 2 := by
    have ht := mul_le_mul_of_nonneg_right hzhsq (sq_nonneg (sin alpha))
    rw [hhsq] at ht
    simpa only [mul_comm] using ht
  have hDz : sin alpha ^ 2 * A - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha ≤ 0 := by
    calc
      _ = D - sin alpha ^ 2 * z ^ 2 := by dsimp only [A, D]; ring
      _ ≤ 0 := sub_nonpos.mpr hmul
  have hpoly : P ^ 2 - X ^ 2 =
      A * (sin alpha ^ 2 * A - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) := by
    dsimp only [P, X]
    rw [mul_pow, hb2, hd2]
    linear_combination -(A ^ 2) * sin_sq_add_cos_sq alpha
  have hrel : P ^ 2 ≤ X ^ 2 := by
    have ht := mul_nonpos_of_nonneg_of_nonpos hA.le hDz
    rw [← hpoly] at ht
    exact sub_nonpos.mp ht
  have hangle (u v : ℝ) (hu0 : 0 ≤ u) (hup : u ≤ π)
      (hv0 : 0 ≤ v) (hvp : v ≤ π) (hc : cos u ≤ cos v) : v ≤ u := by
    by_contra hn
    have ht := cos_lt_cos_of_nonneg_of_le_pi hu0 hvp (lt_of_not_ge hn)
    exact (not_lt_of_ge hc) ht
  have hcontain (hX : 0 ≤ X) : cos (f - g) ≤ cos alpha := by
    have hPX : P ≤ X := (sq_le_sq₀ hP hX).mp hrel
    rw [hminuscos]
    apply (div_le_iff₀ hA).mpr
    dsimp only [X] at hPX
    linarith only [hPX]
  have hdisjoint (hX : X ≤ 0) : f + g ≤ alpha := by
    have hPX : P ≤ -X := (sq_le_sq₀ hP (neg_nonneg.mpr hX)).mp (by
      simpa only [neg_sq] using hrel)
    have hc : cos alpha ≤ cos (f + g) := by
      rw [hpluscos]
      apply (le_div_iff₀ hA).mpr
      dsimp only [X] at hPX
      linarith only [hPX]
    exact hangle alpha (f + g) ha0.le hap.le (add_nonneg hf0 hg0) (by linarith only [hfp, hgp]) hc
  by_cases hkcase : l < k * cos alpha
  · rw [if_pos hkcase]
    have hc0 : 0 ≤ cos alpha := by
      by_contra hn
      have ht := mul_nonpos_of_nonneg_of_nonpos hk0.le (le_of_lt (lt_of_not_ge hn))
      linarith only [ht, hkcase, hl0]
    have hkl : l ≤ k := by
      have ht := mul_le_mul_of_nonneg_left (cos_le_one alpha) hk0.le
      nlinarith only [hkcase, ht]
    have hfg : f ≤ g := arccos_le_arccos ((div_le_div_iff_of_pos_right hr).mpr hkl)
    have hX : 0 ≤ X := by
      have ht := mul_nonneg hAk hc0
      have hkprod := mul_pos hk0 (sub_pos.mpr hkcase)
      dsimp only [X]
      nlinarith only [ht, hkprod]
    have hc : cos (g - f) ≤ cos alpha := by
      rw [← cos_neg (g - f), neg_sub]
      exact hcontain hX
    have hdiff : alpha ≤ g - f := hangle (g - f) alpha (sub_nonneg.mpr hfg)
      (by linarith only [hgp, hf0, pi_pos]) ha0.le hap.le hc
    have hfirst : 2 * f ≤ 2 * g := by linarith only [hfg]
    have hsecond : 2 * f ≤ f + g - alpha := by linarith only [hdiff]
    rw [← min_assoc, min_eq_left hfirst, min_eq_left hsecond, max_eq_right (by positivity)]
  · rw [if_neg hkcase]
    by_cases hlcase : k < l * cos alpha
    · rw [if_pos hlcase]
      have hc0 : 0 ≤ cos alpha := by
        by_contra hn
        have ht := mul_nonpos_of_nonneg_of_nonpos hl0.le (le_of_lt (lt_of_not_ge hn))
        linarith only [ht, hlcase, hk0]
      have hlk : k ≤ l := by
        have ht := mul_le_mul_of_nonneg_left (cos_le_one alpha) hl0.le
        nlinarith only [hlcase, ht]
      have hgf : g ≤ f := arccos_le_arccos ((div_le_div_iff_of_pos_right hr).mpr hlk)
      have hX : 0 ≤ X := by
        have ht := mul_nonneg hAl hc0
        have hlprod := mul_pos hl0 (sub_pos.mpr hlcase)
        dsimp only [X]
        nlinarith only [ht, hlprod]
      have hdiff : alpha ≤ f - g := hangle (f - g) alpha (sub_nonneg.mpr hgf)
        (by linarith only [hfp, hg0, pi_pos]) ha0.le hap.le (hcontain hX)
      have hfirst : 2 * g ≤ 2 * f := by linarith only [hgf]
      have hsecond : 2 * g ≤ f + g - alpha := by linarith only [hdiff]
      rw [min_eq_left hsecond, min_eq_right hfirst, max_eq_right (by positivity)]
    · rw [if_neg hlcase]
      have hX : X ≤ 0 := by
        by_cases hc0 : 0 ≤ cos alpha
        · have hprod : 0 ≤ (l - k * cos alpha) * (k - l * cos alpha) :=
            mul_nonneg (sub_nonneg.mpr (le_of_not_gt hkcase)) (sub_nonneg.mpr (le_of_not_gt hlcase))
          have ht := mul_nonpos_of_nonneg_of_nonpos hc0 hDz
          have hid : sin alpha ^ 2 * X =
              cos alpha * (sin alpha ^ 2 * A - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) -
                (l - k * cos alpha) * (k - l * cos alpha) := by
            dsimp only [X]
            linear_combination -(k * l) * sin_sq_add_cos_sq alpha
          have hn : sin alpha ^ 2 * X ≤ 0 := by linarith only [ht, hprod, hid]
          by_contra hx
          have hp := mul_pos (sq_pos_of_pos hs) (lt_of_not_ge hx)
          linarith only [hn, hp]
        · have ht := mul_nonpos_of_nonneg_of_nonpos hA.le (le_of_lt (lt_of_not_ge hc0))
          have hp := mul_pos hk0 hl0
          dsimp only [X]
          linarith only [ht, hp]
      have hsum := hdisjoint hX
      have hmin : min (2 * f) (min (2 * g) (f + g - alpha)) ≤ 0 :=
        le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith only [hsum])
      exact max_eq_left hmin
