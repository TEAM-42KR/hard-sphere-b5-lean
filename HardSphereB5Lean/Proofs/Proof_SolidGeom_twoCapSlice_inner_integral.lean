import Mathlib
set_option autoImplicit false

open MeasureTheory Real
set_option maxHeartbeats 800000

private theorem twoCap_threshold_aux (k l alpha : ℝ)
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

open MeasureTheory Real
set_option maxHeartbeats 1600000

private theorem twoCap_branch_aux (k l alpha z : ℝ)
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

set_option maxHeartbeats 900000

private theorem sliceCap_antideriv_aux (k z : ℝ) (hk0 : 0 < k) (hk1 : k < 1)
    (hz : z ^ 2 < 1 - k ^ 2) :
    HasDerivAt (fun t : ℝ => t * Real.arccos (k / Real.sqrt (1 - t ^ 2)) +
      Real.arctan (k * t / Real.sqrt (1 - k ^ 2 - t ^ 2)) -
      k * Real.arcsin (t / Real.sqrt (1 - k ^ 2)))
      (Real.arccos (k / Real.sqrt (1 - z ^ 2))) z := by
  let a := Real.sqrt (1 - z ^ 2)
  let b := Real.sqrt (1 - k ^ 2 - z ^ 2)
  let c := Real.sqrt (1 - k ^ 2)
  have hC : 0 < 1 - k ^ 2 := by
    have := (sq_lt_sq₀ (le_of_lt hk0) (by norm_num : (0 : ℝ) ≤ 1)).2 hk1
    nlinarith
  have hA : 0 < 1 - z ^ 2 := by nlinarith [sq_nonneg k]
  have hB : 0 < 1 - k ^ 2 - z ^ 2 := by linarith
  have ha : 0 < a := Real.sqrt_pos.2 hA
  have hb : 0 < b := Real.sqrt_pos.2 hB
  have hc : 0 < c := Real.sqrt_pos.2 hC
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hasq : a ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hA.le
  have hbsq : b ^ 2 = 1 - k ^ 2 - z ^ 2 := Real.sq_sqrt hB.le
  have hcsq : c ^ 2 = 1 - k ^ 2 := Real.sq_sqrt hC.le
  have hcos_sq : (k / a) ^ 2 < 1 := by
    rw [div_pow]
    apply (div_lt_one (pow_pos ha 2)).2
    rw [hasq]
    linarith
  have hcos_neg : k / a ≠ -1 := by
    intro h; rw [h] at hcos_sq; norm_num at hcos_sq
  have hcos_one : k / a ≠ 1 := by
    intro h; rw [h] at hcos_sq; norm_num at hcos_sq
  have hsin_sq : (z / c) ^ 2 < 1 := by
    rw [div_pow]
    apply (div_lt_one (pow_pos hc 2)).2
    simpa only [hcsq] using hz
  have hsin_neg : z / c ≠ -1 := by
    intro h; rw [h] at hsin_sq; norm_num at hsin_sq
  have hsin_one : z / c ≠ 1 := by
    intro h; rw [h] at hsin_sq; norm_num at hsin_sq
  have hcos_rad : 1 - (k / a) ^ 2 = (1 - k ^ 2 - z ^ 2) / (1 - z ^ 2) := by
    rw [div_pow, hasq]
    field_simp [ne_of_gt hA] <;> ring
  have hsin_rad : 1 - (z / c) ^ 2 = (1 - k ^ 2 - z ^ 2) / (1 - k ^ 2) := by
    rw [div_pow, hcsq]
    field_simp [ne_of_gt hC] <;> ring
  have hcos_sqrt : Real.sqrt (1 - (k / a) ^ 2) = b / a := by
    rw [hcos_rad, Real.sqrt_div hB.le]
  have hsin_sqrt : Real.sqrt (1 - (z / c) ^ 2) = b / c := by
    rw [hsin_rad, Real.sqrt_div hB.le]
  have dz2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
    convert! (hasDerivAt_id z).pow 2 using 1 <;> simp <;> ring
  have da : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2)) (-z / a) z := by
    convert! (dz2.const_sub 1).sqrt (ne_of_gt hA) using 1
    dsimp [a]
    field_simp [ha0, hb0, hc0] <;> ring
  have db : HasDerivAt (fun t : ℝ => Real.sqrt (1 - k ^ 2 - t ^ 2)) (-z / b) z := by
    convert! (dz2.const_sub (1 - k ^ 2)).sqrt (ne_of_gt hB) using 1
    dsimp [b]
    field_simp [ha0, hb0, hc0] <;> ring
  have dka : HasDerivAt (fun t : ℝ => k / Real.sqrt (1 - t ^ 2))
      (k * z / a ^ 3) z := by
    convert! (hasDerivAt_const z k).div da ha0 using 1
    change k * z / a ^ 3 = (0 * a - k * (-z / a)) / a ^ 2
    field_simp [ha0, hb0, hc0] <;> ring
  have dcos : HasDerivAt (fun t : ℝ => Real.arccos (k / Real.sqrt (1 - t ^ 2)))
      (-k * z / (a ^ 2 * b)) z := by
    convert! (Real.hasDerivAt_arccos hcos_neg hcos_one).comp z dka using 1
    change -k * z / (a ^ 2 * b) = -(1 / Real.sqrt (1 - (k / a) ^ 2)) * (k * z / a ^ 3)
    rw [hcos_sqrt]
    field_simp [ha0, hb0, hc0] <;> ring
  have hbc : b ^ 2 + z ^ 2 = c ^ 2 := by rw [hbsq, hcsq]; ring
  have dkb : HasDerivAt (fun t : ℝ => k * t / Real.sqrt (1 - k ^ 2 - t ^ 2))
      (k * c ^ 2 / b ^ 3) z := by
    convert! ((hasDerivAt_id z).const_mul k).div db hb0 using 1
    simp only [mul_one, id_eq]
    change k * c ^ 2 / b ^ 3 = (k * b - k * z * (-z / b)) / b ^ 2
    calc
      k * c ^ 2 / b ^ 3 = k * (b ^ 2 + z ^ 2) / b ^ 3 := by rw [hbc]
      _ = (k * b - k * z * (-z / b)) / b ^ 2 := by field_simp; ring
  have htan_den : 1 + (k * z / b) ^ 2 = a ^ 2 * c ^ 2 / b ^ 2 := by
    rw [div_pow]
    field_simp [hb0]
    rw [hasq, hbsq, hcsq]
    ring
  have dtan : HasDerivAt (fun t : ℝ => Real.arctan (k * t / Real.sqrt (1 - k ^ 2 - t ^ 2)))
      (k / (a ^ 2 * b)) z := by
    convert! dkb.arctan using 1
    change k / (a ^ 2 * b) = 1 / (1 + (k * z / b) ^ 2) * (k * c ^ 2 / b ^ 3)
    rw [htan_den]
    field_simp [ha0, hb0, hc0] <;> ring
  have dsin : HasDerivAt (fun t : ℝ => Real.arcsin (t / Real.sqrt (1 - k ^ 2)))
      (1 / b) z := by
    convert! (Real.hasDerivAt_arcsin hsin_neg hsin_one).comp z
      ((hasDerivAt_id z).div_const c) using 1
    change 1 / b = 1 / Real.sqrt (1 - (z / c) ^ 2) * (1 / c)
    rw [hsin_sqrt]
    field_simp
  convert! (((hasDerivAt_id z).mul dcos).add dtan).sub (dsin.const_mul k) using 1
  change Real.arccos (k / a) =
    1 * Real.arccos (k / a) + z * (-k * z / (a ^ 2 * b)) +
      k / (a ^ 2 * b) - k * (1 / b)
  field_simp [ha0, hb0]
  rw [hasq]
  ring

open MeasureTheory

private theorem sliceCap_integral_aux (k h : ℝ) (hk0 : 0 < k) (hk1 : k < 1) (hh0 : 0 ≤ h)
    (hh : h ^ 2 < 1 - k ^ 2) :
    (∫ z in (0 : ℝ)..h, Real.arccos (k / Real.sqrt (1 - z ^ 2))) =
      h * Real.arccos (k / Real.sqrt (1 - h ^ 2)) +
        Real.arctan (k * h / Real.sqrt (1 - k ^ 2 - h ^ 2)) -
        k * Real.arcsin (h / Real.sqrt (1 - k ^ 2)) := by
  let f : ℝ → ℝ := fun z => Real.arccos (k / Real.sqrt (1 - z ^ 2))
  let F : ℝ → ℝ := fun z => z * Real.arccos (k / Real.sqrt (1 - z ^ 2)) +
    Real.arctan (k * z / Real.sqrt (1 - k ^ 2 - z ^ 2)) -
    k * Real.arcsin (z / Real.sqrt (1 - k ^ 2))
  have hx2 (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) h) : x ^ 2 < 1 - k ^ 2 := by
    rw [Set.uIcc_of_le hh0] at hx
    have hsq : x ^ 2 ≤ h ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hh0 hx.1)]
    exact lt_of_le_of_lt hsq hh
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) h, HasDerivAt F (f x) x := by
    intro x hx
    exact sliceCap_antideriv_aux k x hk0 hk1 (hx2 x hx)
  have hcont : ContinuousOn f (Set.uIcc (0 : ℝ) h) := by
    intro x hx
    have hroot : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 (by
      have := hx2 x hx
      nlinarith [sq_nonneg k])
    have hratio : ContinuousAt (fun z : ℝ => k / Real.sqrt (1 - z ^ 2)) x :=
      continuousAt_const.div ((continuousAt_const.sub (continuousAt_id.pow 2)).sqrt) hroot
    exact (Real.continuous_arccos.continuousAt.comp hratio).continuousWithinAt
  have hint : IntervalIntegrable f volume (0 : ℝ) h := hcont.intervalIntegrable
  have hF0 : F 0 = 0 := by simp [F]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa only [hF0, sub_zero] using hFTC

open Real

private theorem twoCap_partial_aux (k l alpha t : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ht0 : 0 ≤ t) (htk : t ^ 2 < 1 - k ^ 2) (htl : t ^ 2 < 1 - l ^ 2) :
    (∫ z in (0 : ℝ)..t, arccos (k / sqrt (1 - z ^ 2)) +
      arccos (l / sqrt (1 - z ^ 2)) - alpha) =
      t * (arccos (k / sqrt (1 - t ^ 2)) + arccos (l / sqrt (1 - t ^ 2)) - alpha) +
      arctan (k * t / sqrt (1 - k ^ 2 - t ^ 2)) +
      arctan (l * t / sqrt (1 - l ^ 2 - t ^ 2)) -
      k * arcsin (t / sqrt (1 - k ^ 2)) - l * arcsin (t / sqrt (1 - l ^ 2)) := by
  have hi (r : ℝ) (htr : t ^ 2 < 1 - r ^ 2) :
      IntervalIntegrable (fun z : ℝ => arccos (r / sqrt (1 - z ^ 2))) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le ht0] at hx
    have hx2 : x ^ 2 ≤ t ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg ht0 hx.1)]
    have hroot : sqrt (1 - x ^ 2) ≠ 0 := sqrt_ne_zero'.mpr (by
      nlinarith [sq_nonneg r])
    exact (continuous_arccos.continuousAt.comp
      (continuousAt_const.div ((continuousAt_const.sub (continuousAt_id.pow 2)).sqrt)
        hroot)).continuousWithinAt
  rw [intervalIntegral.integral_sub ((hi k htk).add (hi l htl)) intervalIntegrable_const,
    intervalIntegral.integral_add (hi k htk) (hi l htl),
    sliceCap_integral_aux k t hk0 hk1 ht0 htk,
    sliceCap_integral_aux l t hl0 hl1 ht0 htl,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

set_option maxHeartbeats 1600000
open MeasureTheory Real

theorem proof_SolidGeom_twoCapSlice_inner_integral (k l alpha t : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)
    (ht0 : 0 ≤ t)
    (ht : t ^ 2 < (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) / sin alpha ^ 2) :
    (∫ z in (0 : ℝ)..t, max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
      (min (2 * arccos (l / sqrt (1 - z ^ 2)))
        (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha)))) =
      t * (arccos (k / sqrt (1 - t ^ 2)) + arccos (l / sqrt (1 - t ^ 2)) - alpha) +
      arctan (k * t / sqrt (1 - k ^ 2 - t ^ 2)) +
      arctan (l * t / sqrt (1 - l ^ 2 - t ^ 2)) -
      k * arcsin (t / sqrt (1 - k ^ 2)) - l * arcsin (t / sqrt (1 - l ^ 2)) := by
  let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
  let h := sqrt D / sin alpha
  have hs : 0 < sin alpha := sin_pos_of_pos_of_lt_pi ha0 hap
  have hht : h ^ 2 = D / sin alpha ^ 2 := by
    dsimp [h]
    rw [div_pow, sq_sqrt hD.le]
  have ht1 : t ^ 2 < h ^ 2 := by rwa [hht]
  rcases twoCap_threshold_aux k l alpha hk0 hk1 hl0 hl1 ha0 hap hD with
    ⟨hh0, hhH, hkEq, hlEq⟩
  have htk : t ^ 2 < 1 - k ^ 2 := by
    have hn : 0 ≤ (l - k * cos alpha) ^ 2 / sin alpha ^ 2 := by positivity
    change 1 - k ^ 2 - h ^ 2 = _ at hkEq
    linarith only [ht1, hkEq, hn]
  have htl : t ^ 2 < 1 - l ^ 2 := by
    have hn : 0 ≤ (k - l * cos alpha) ^ 2 / sin alpha ^ 2 := by positivity
    change 1 - l ^ 2 - h ^ 2 = _ at hlEq
    linarith only [ht1, hlEq, hn]
  have heq :
      (∫ z in (0 : ℝ)..t, max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
        (min (2 * arccos (l / sqrt (1 - z ^ 2)))
          (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha)))) =
      (∫ z in (0 : ℝ)..t, arccos (k / sqrt (1 - z ^ 2)) +
        arccos (l / sqrt (1 - z ^ 2)) - alpha) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ht0] at hx
    have hx2 : x ^ 2 ≤ t ^ 2 := by
      nlinarith only [hx.1, hx.2, ht0, mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg ht0 hx.1)]
    have htD : t ^ 2 * sin alpha ^ 2 < D := (lt_div_iff₀ (sq_pos_of_pos hs)).mp ht
    have hxD := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hx2 (sq_nonneg (sin alpha))) htD
    have hxpos : 0 < sin alpha ^ 2 * (1 - x ^ 2) - k ^ 2 - l ^ 2 +
        2 * k * l * cos alpha := by
      dsimp [D] at hxD
      nlinarith only [hxD]
    exact twoCap_branch_aux k l alpha x hk0 hk1 hl0 hl1 ha0 hap
      (lt_of_le_of_lt hx2 htk) (lt_of_le_of_lt hx2 htl) hxpos
  rw [heq]
  exact twoCap_partial_aux k l alpha t hk0 hk1 hl0 hl1 ht0 htk htl
