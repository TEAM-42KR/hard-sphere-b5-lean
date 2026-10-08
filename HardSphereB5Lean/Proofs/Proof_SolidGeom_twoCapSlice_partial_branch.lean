import Mathlib
set_option autoImplicit false
open MeasureTheory Real
set_option maxHeartbeats 1600000

theorem proof_SolidGeom_twoCapSlice_partial_branch (k l alpha z : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hzk : z ^ 2 < 1 - k ^ 2) (hzl : z ^ 2 < 1 - l ^ 2)
    (hDz : 0 < sin alpha ^ 2 * (1 - z ^ 2) - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) :
    max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
      (min (2 * arccos (l / sqrt (1 - z ^ 2)))
        (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha))) =
      arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha := by
  let A := 1 - z ^ 2
  let r := sqrt A
  let b := sqrt (A - k ^ 2)
  let d := sqrt (A - l ^ 2)
  let f := arccos (k / r)
  let g := arccos (l / r)
  change max 0 (min (2 * f) (min (2 * g) (f + g - alpha))) = f + g - alpha
  have hA : 0 < A := by dsimp [A]; nlinarith [sq_nonneg k]
  have hAk : 0 < A - k ^ 2 := by dsimp [A]; linarith
  have hAl : 0 < A - l ^ 2 := by dsimp [A]; linarith
  have hr : 0 < r := sqrt_pos.mpr hA
  have hb : 0 < b := sqrt_pos.mpr hAk
  have hd : 0 < d := sqrt_pos.mpr hAl
  have hr2 : r ^ 2 = A := sq_sqrt hA.le
  have hb2 : b ^ 2 = A - k ^ 2 := sq_sqrt hAk.le
  have hd2 : d ^ 2 = A - l ^ 2 := sq_sqrt hAl.le
  have hkr : 0 < k / r := div_pos hk0 hr
  have hlr : 0 < l / r := div_pos hl0 hr
  have hkr1 : k / r < 1 := (div_lt_one hr).mpr (by nlinarith)
  have hlr1 : l / r < 1 := (div_lt_one hr).mpr (by nlinarith)
  have hf0 : 0 < f := arccos_pos.mpr hkr1
  have hg0 : 0 < g := arccos_pos.mpr hlr1
  have hfp : f < π / 2 := arccos_lt_pi_div_two.mpr hkr
  have hgp : g < π / 2 := arccos_lt_pi_div_two.mpr hlr
  have hcf : cos f = k / r := cos_arccos (by linarith) hkr1.le
  have hcg : cos g = l / r := cos_arccos (by linarith) hlr1.le
  have hsf : sin f = b / r := by
    dsimp [f]
    rw [sin_arccos]
    have he : 1 - (k / r) ^ 2 = (A - k ^ 2) / A := by
      rw [div_pow, hr2]
      field_simp [ne_of_gt hA] <;> ring
    rw [he, sqrt_div hAk.le]
  have hsg : sin g = d / r := by
    dsimp [g]
    rw [sin_arccos]
    have he : 1 - (l / r) ^ 2 = (A - l ^ 2) / A := by
      rw [div_pow, hr2]
      field_simp [ne_of_gt hA] <;> ring
    rw [he, sqrt_div hAl.le]
  let P := b * d
  let X := A * cos alpha - k * l
  have hP : 0 < P := mul_pos hb hd
  have hpoly : P ^ 2 - X ^ 2 =
      A * (sin alpha ^ 2 * A - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) := by
    dsimp only [P, X]
    rw [mul_pow, hb2, hd2]
    have hc := sin_sq_add_cos_sq alpha
    linear_combination -(A ^ 2) * hc
  have hrel : X ^ 2 < P ^ 2 := by
    have hp := mul_pos hA hDz
    change 0 < A * (sin alpha ^ 2 * A - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) at hp
    rw [← hpoly] at hp
    exact sub_pos.mp hp
  have haX : |X| < P := by simpa only [abs_of_pos hP] using (sq_lt_sq.mp hrel)
  have hupper : X < P := (abs_lt.mp haX).2
  have hlower : -P < X := (abs_lt.mp haX).1
  have hcplus : cos (f + g) = (k * l - P) / A := by
    rw [cos_add, hcf, hcg, hsf, hsg]
    dsimp only [P]
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← pow_two, hr2]
  have hcminus : cos (f - g) = (k * l + P) / A := by
    rw [cos_sub, hcf, hcg, hsf, hsg]
    dsimp only [P]
    rw [div_mul_div_comm, div_mul_div_comm, ← add_div, ← pow_two, hr2]
  have hplus : alpha < f + g := by
    have hc : cos (f + g) < cos alpha := by
      rw [hcplus]
      apply (div_lt_iff₀ hA).mpr
      dsimp [X] at hlower
      nlinarith
    by_contra hn
    have ht := cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ f + g) hap.le
      (le_of_not_gt hn)
    linarith
  have hminus : |f - g| < alpha := by
    have hc : cos alpha < cos |f - g| := by
      rw [cos_abs, hcminus]
      apply (lt_div_iff₀ hA).mpr
      dsimp [X] at hupper
      nlinarith
    by_contra hn
    have hp : |f - g| ≤ π := abs_le.mpr ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have ht := cos_le_cos_of_nonneg_of_le_pi ha0.le hp
      (le_of_not_gt hn)
    linarith
  have hdiff := abs_lt.mp hminus
  have h1 : f + g - alpha ≤ 2 * f := by linarith
  have h2 : f + g - alpha ≤ 2 * g := by linarith
  rw [min_eq_right h2, min_eq_right h1, max_eq_right (by linarith)]
