import Mathlib
import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_sqrt_disk_tail_arg_shift
set_option autoImplicit false

open MeasureTheory

set_option maxHeartbeats 800000

theorem proof_SphereGeom_two_cap_transverse_closed (A K L : ℝ) (hA0 : 0 < A) (hA2 : A < 2) (hL : 0 < L)
    (hB2 : K ^ 2 + L ^ 2 < 4)
    (hH : 0 < L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2) :
    let B := Real.sqrt (K ^ 2 + L ^ 2)
    let H := L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2
    (2 / L) * (∫ t in (A / 2)..1,
      Real.sqrt (L ^ 2 * (1 - t ^ 2) - ((K ^ 2 + L ^ 2) / 2 - K * t) ^ 2)) =
      ((1 - B ^ 2 / 4) * L / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ -
        Real.sqrt H * (A - K) / (2 * L) := by
  let B := Real.sqrt (K ^ 2 + L ^ 2)
  let H := L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2
  change (2 / L) * (∫ t in (A / 2)..1,
      Real.sqrt (L ^ 2 * (1 - t ^ 2) - ((K ^ 2 + L ^ 2) / 2 - K * t) ^ 2)) =
      ((1 - B ^ 2 / 4) * L / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ -
        Real.sqrt H * (A - K) / (2 * L)
  change 0 < H at hH
  have hCpos : 0 < K ^ 2 + L ^ 2 := by nlinarith [sq_nonneg K, sq_pos_of_pos hL]
  have hB : 0 < B := Real.sqrt_pos.mpr hCpos
  have hBn : B ≠ 0 := ne_of_gt hB
  have hLn : L ≠ 0 := ne_of_gt hL
  have hBs : B ^ 2 = K ^ 2 + L ^ 2 := Real.sq_sqrt hCpos.le
  have hBlt : B < 2 := by nlinarith
  have hKB : K ≤ B := by nlinarith [sq_nonneg L, sq_nonneg (B - K)]
  have hc : 0 < 1 - B ^ 2 / 4 := by nlinarith
  let q := Real.sqrt (1 - B ^ 2 / 4)
  let r := (L / B) * q
  let d := K / 2
  have hq : 0 < q := Real.sqrt_pos.mpr hc
  have hqs : q ^ 2 = 1 - B ^ 2 / 4 := Real.sq_sqrt hc.le
  have hr : 0 < r := mul_pos (div_pos hL hB) hq
  have hBr : B * r = L * q := by
    dsimp only [r]
    field_simp
  have hrs : B ^ 2 * r ^ 2 = L ^ 2 * (1 - B ^ 2 / 4) := by
    calc
      B ^ 2 * r ^ 2 = (B * r) ^ 2 := by ring
      _ = (L * q) ^ 2 := by rw [hBr]
      _ = L ^ 2 * (1 - B ^ 2 / 4) := by rw [mul_pow, hqs]
  have hkernel (t : ℝ) :
      L ^ 2 * (1 - t ^ 2) - ((K ^ 2 + L ^ 2) / 2 - K * t) ^ 2 =
        B ^ 2 * (r ^ 2 - (t - d) ^ 2) := by
    dsimp only [d]
    rw [← hBs]
    linear_combination -hrs + (t ^ 2 - B ^ 2 / 4) * hBs
  have hHid : H = B ^ 2 * (r ^ 2 - (A / 2 - d) ^ 2) := by
    calc
      H = L ^ 2 * (1 - (A / 2) ^ 2) -
          ((K ^ 2 + L ^ 2) / 2 - K * (A / 2)) ^ 2 := by dsimp only [H]; ring
      _ = B ^ 2 * (r ^ 2 - (A / 2 - d) ^ 2) := hkernel (A / 2)
  have hD : 0 < r ^ 2 - (A / 2 - d) ^ 2 := by
    have hh : 0 < B ^ 2 * (r ^ 2 - (A / 2 - d) ^ 2) := by rw [← hHid]; exact hH
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hB)).mp hh
  have hh0 : -r < A / 2 - d := by nlinarith [sq_nonneg (r + (A / 2 - d))]
  have hh1 : A / 2 - d < r := by nlinarith [sq_nonneg (r - (A / 2 - d))]
  have hd : d < 1 := by dsimp only [d]; linarith
  have hedge : B ^ 2 * ((1 - d) ^ 2 - r ^ 2) = (K - B ^ 2 / 2) ^ 2 := by
    dsimp only [d]
    linear_combination -hrs + (1 - B ^ 2 / 4) * hBs
  have hedge0 : 0 ≤ (1 - d) ^ 2 - r ^ 2 := by
    have hh : 0 ≤ B ^ 2 * ((1 - d) ^ 2 - r ^ 2) := by rw [hedge]; positivity
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hB)).mp hh
  have hb : d + r ≤ 1 := by nlinarith [sq_nonneg (1 - d - r)]
  have hroot (t : ℝ) :
      Real.sqrt (L ^ 2 * (1 - t ^ 2) - ((K ^ 2 + L ^ 2) / 2 - K * t) ^ 2) =
        B * Real.sqrt (r ^ 2 - (t - d) ^ 2) := by
    rw [hkernel, Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le]
  have hsqrtH : Real.sqrt H = B * Real.sqrt (r ^ 2 - (A / 2 - d) ^ 2) := by
    rw [hHid, Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le]
  have hsD : Real.sqrt (r ^ 2 - (A / 2 - d) ^ 2) = Real.sqrt H / B := by
    rw [hsqrtH]
    field_simp
  have hr2 : r ^ 2 = (1 - B ^ 2 / 4) * L ^ 2 / B ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hBn)).mpr
    nlinarith [hrs]
  have harg : Complex.arg ⟨A / 2 - d, Real.sqrt (r ^ 2 - (A / 2 - d) ^ 2)⟩ =
      Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ := by
    have he : (⟨B * (A - K), 2 * Real.sqrt H⟩ : ℂ) =
        ((2 * B : ℝ) : ℂ) * ⟨A / 2 - d, Real.sqrt (r ^ 2 - (A / 2 - d) ^ 2)⟩ := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        dsimp only [d]
        ring
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero]
        rw [hsqrtH]
        ring
    rw [he, Complex.arg_real_mul _ (by positivity)]
  have hint := SphereGeom.integral_sqrt_disk_tail_arg_shift r d (A / 2) 1 hr hh0 hh1 hb
  calc
    (2 / L) * (∫ t in (A / 2)..1,
        Real.sqrt (L ^ 2 * (1 - t ^ 2) - ((K ^ 2 + L ^ 2) / 2 - K * t) ^ 2)) =
        (2 / L) * (B * (∫ t in (A / 2)..1, Real.sqrt (r ^ 2 - (t - d) ^ 2))) := by
      simp_rw [hroot]
      rw [intervalIntegral.integral_const_mul]
    _ = ((1 - B ^ 2 / 4) * L / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ -
          Real.sqrt H * (A - K) / (2 * L) := by
      rw [hint, harg, hsD, hr2]
      dsimp only [d]
      field_simp
      <;> ring
