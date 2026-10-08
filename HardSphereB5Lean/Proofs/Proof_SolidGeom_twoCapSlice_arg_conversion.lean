import Mathlib
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_threshold
set_option autoImplicit false
open MeasureTheory Real

theorem proof_SolidGeom_twoCapSlice_arg_conversion (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) :
    let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
    let h := sqrt D / sin alpha
    let Ck := sqrt (1 - k ^ 2)
    let Cl := sqrt (1 - l ^ 2)
    let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
    let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
    let Xk := l - k * cos alpha
    let Xl := k - l * cos alpha
    let Tk := if Xk = 0 then π / 2 else arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2))
    let Tl := if Xl = 0 then π / 2 else arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2))
    Complex.arg ⟨Xk, sqrt D⟩ =
        (if Xk < 0 then π - arcsin (h / Ck) else arcsin (h / Ck)) ∧
      Complex.arg ⟨Xl, sqrt D⟩ =
        (if Xl < 0 then π - arcsin (h / Cl) else arcsin (h / Cl)) ∧
      Complex.arg ⟨cos alpha - k * l, sqrt D⟩ =
        (if Xk < 0 then Tk - Tl else if Xl < 0 then Tl - Tk else π - Tk - Tl) := by
  dsimp only
  let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
  let S := sin alpha
  let u := sqrt D
  let h := u / S
  let Ck := sqrt (1 - k ^ 2)
  let Cl := sqrt (1 - l ^ 2)
  let X := l - k * cos alpha
  let Y := k - l * cos alpha
  let Tk := if X = 0 then π / 2 else arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2))
  let Tl := if Y = 0 then π / 2 else arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2))
  change Complex.arg ⟨X, u⟩ = (if X < 0 then π - arcsin (h / Ck) else arcsin (h / Ck)) ∧
    Complex.arg ⟨Y, u⟩ = (if Y < 0 then π - arcsin (h / Cl) else arcsin (h / Cl)) ∧
    Complex.arg ⟨cos alpha - k * l, u⟩ =
      (if X < 0 then Tk - Tl else if Y < 0 then Tl - Tk else π - Tk - Tl)
  have hS : 0 < S := sin_pos_of_pos_of_lt_pi ha0 hap
  have hDp : 0 < D := hD
  have hu : 0 < u := sqrt_pos.mpr hDp
  have hu2 : u ^ 2 = D := sq_sqrt hDp.le
  have hkk : 0 < 1 - k ^ 2 := by nlinarith only [hk0, hk1]
  have hll : 0 < 1 - l ^ 2 := by nlinarith only [hl0, hl1]
  have hCk : 0 < Ck := sqrt_pos.mpr hkk
  have hCl : 0 < Cl := sqrt_pos.mpr hll
  have hCk2 : Ck ^ 2 = 1 - k ^ 2 := sq_sqrt hkk.le
  have hCl2 : Cl ^ 2 = 1 - l ^ 2 := sq_sqrt hll.le
  have hthr := SolidGeom.twoCapSlice_threshold k l alpha hk0 hk1 hl0 hl1 ha0 hap hD
  change 0 < h ∧ h ≤ min Ck Cl ∧
    1 - k ^ 2 - h ^ 2 = X ^ 2 / S ^ 2 ∧
    1 - l ^ 2 - h ^ 2 = Y ^ 2 / S ^ 2 at hthr
  obtain ⟨hh, hbound, htk, htl⟩ := hthr
  have radk : X ^ 2 + D = S ^ 2 * (1 - k ^ 2) := by
    dsimp only [X, D, S]
    linear_combination k ^ 2 * sin_sq_add_cos_sq alpha
  have radl : Y ^ 2 + D = S ^ 2 * (1 - l ^ 2) := by
    dsimp only [Y, D, S]
    linear_combination l ^ 2 * sin_sq_add_cos_sq alpha
  have hnorm (x r : ℝ) (hr : 0 < r) (he : x ^ 2 + D = S ^ 2 * r ^ 2) :
      ‖(⟨x, u⟩ : ℂ)‖ = S * r := by
    have hs : ‖(⟨x, u⟩ : ℂ)‖ ^ 2 = (S * r) ^ 2 := by
      calc
        ‖(⟨x, u⟩ : ℂ)‖ ^ 2 = x ^ 2 + u ^ 2 := by
          rw [Complex.sq_norm]
          change x * x + u * u = x ^ 2 + u ^ 2
          ring
        _ = S ^ 2 * r ^ 2 := by rw [hu2]; exact he
        _ = (S * r) ^ 2 := by ring
    exact (sq_eq_sq₀ (norm_nonneg _) (mul_pos hS hr).le).mp hs
  have normk : ‖(⟨X, u⟩ : ℂ)‖ = S * Ck :=
    hnorm X Ck hCk (by rw [hCk2]; exact radk)
  have norml : ‖(⟨Y, u⟩ : ℂ)‖ = S * Cl :=
    hnorm Y Cl hCl (by rw [hCl2]; exact radl)
  have hargsin (x r : ℝ) (hr : 0 < r) (hn : ‖(⟨x, u⟩ : ℂ)‖ = S * r) :
      Complex.arg ⟨x, u⟩ = (if x < 0 then π - arcsin (h / r) else arcsin (h / r)) := by
    have hquot : u / (S * r) = h / r := by
      dsimp only [h]
      field_simp
    by_cases hx : x < 0
    · rw [if_pos hx, Complex.arg_of_re_neg_of_im_nonneg hx hu.le]
      change arcsin (-u / ‖(⟨x, u⟩ : ℂ)‖) + π = π - arcsin (h / r)
      rw [hn, neg_div, arcsin_neg, hquot]
      ring
    · rw [if_neg hx, Complex.arg_of_re_nonneg (show 0 ≤ x from le_of_not_gt hx)]
      change arcsin (u / ‖(⟨x, u⟩ : ℂ)‖) = arcsin (h / r)
      rw [hn, hquot]
  have hargk := hargsin X Ck hCk normk
  have hargl := hargsin Y Cl hCl norml
  have hatan (x j : ℝ) (hj : 0 < j)
      (he : 1 - j ^ 2 - h ^ 2 = x ^ 2 / S ^ 2) :
      Complex.arg ⟨|x|, j * u⟩ =
        (if x = 0 then π / 2 else arctan (j * h / sqrt (1 - j ^ 2 - h ^ 2))) := by
    by_cases hx : x = 0
    · rw [if_pos hx]
      exact Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp [hx], mul_pos hj hu⟩
    · rw [if_neg hx]
      have habs : 0 < |x| := abs_pos.mpr hx
      have hroot : sqrt (1 - j ^ 2 - h ^ 2) = |x| / S := by
        rw [he, sqrt_div (sq_nonneg x), sqrt_sq_eq_abs, sqrt_sq hS.le]
      have hr : j * h / sqrt (1 - j ^ 2 - h ^ 2) = j * u / |x| := by
        rw [hroot]
        dsimp only [h]
        field_simp
      rw [hr]
      have hlower : -(π / 2) < Complex.arg (⟨|x|, j * u⟩ : ℂ) :=
        Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl habs)
      have hupper : Complex.arg (⟨|x|, j * u⟩ : ℂ) < π / 2 :=
        Complex.arg_lt_pi_div_two_iff.mpr (Or.inl habs)
      have ht := arctan_tan hlower hupper
      rw [Complex.tan_arg] at ht
      exact ht.symm
  have hreflect (x y : ℝ) (hy : 0 < y) :
      Complex.arg ⟨x, y⟩ =
        (if x < 0 then π - Complex.arg ⟨|x|, y⟩ else Complex.arg ⟨|x|, y⟩) := by
    by_cases hx : x < 0
    · rw [if_pos hx]
      have he : (⟨x, y⟩ : ℂ) = -(starRingEnd ℂ) (⟨|x|, y⟩ : ℂ) := by
        apply Complex.ext <;> simp [abs_of_neg hx]
      have hnp : Complex.arg (⟨|x|, y⟩ : ℂ) ≠ π :=
        ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inr hy.ne'))
      rw [he, Complex.arg_neg_eq_arg_add_pi_of_im_neg, Complex.arg_conj, if_neg hnp]
      · ring
      · change -y < 0
        exact neg_neg_of_pos hy
    · rw [if_neg hx, abs_of_nonneg (le_of_not_gt hx)]
  let zk : ℂ := ⟨X, k * u⟩
  let zl : ℂ := ⟨Y, l * u⟩
  have hzk : 0 < zk.im := mul_pos hk0 hu
  have hzl : 0 < zl.im := mul_pos hl0 hu
  have hbetak : zk.arg = (if X < 0 then π - Tk else Tk) := by
    have ht := hatan X k hk0 htk
    have hr := hreflect X (k * u) hzk
    rw [ht] at hr
    exact hr
  have hbetal : zl.arg = (if Y < 0 then π - Tl else Tl) := by
    have ht := hatan Y l hl0 htl
    have hr := hreflect Y (l * u) hzl
    rw [ht] at hr
    exact hr
  let F := k ^ 2 + l ^ 2 - 2 * k * l * cos alpha
  have hc1 : cos alpha < 1 := by
    have hss : 0 < S ^ 2 := sq_pos_of_pos hS
    have hid := sin_sq_add_cos_sq alpha
    change S ^ 2 + cos alpha ^ 2 = 1 at hid
    nlinarith only [hid, hss, sq_nonneg (cos alpha - 1)]
  have hF : 0 < F := by
    have he : F = (k - l) ^ 2 + 2 * k * l * (1 - cos alpha) := by dsimp only [F]; ring
    rw [he]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)
  have him : (zk * zl).im = F * u := by
    change X * (l * u) + (k * u) * Y = F * u
    dsimp only [X, Y, F]
    ring
  have hpim : 0 < (zk * zl).im := by rw [him]; exact mul_pos hF hu
  have heq : -(starRingEnd ℂ) (zk * zl) =
      (F : ℂ) * (⟨cos alpha - k * l, u⟩ : ℂ) := by
    apply Complex.ext
    · change -(X * Y - (k * u) * (l * u)) = F * (cos alpha - k * l) - 0 * u
      rw [zero_mul, sub_zero]
      calc
        -(X * Y - (k * u) * (l * u)) = -X * Y + k * l * u ^ 2 := by ring
        _ = -X * Y + k * l * D := by rw [hu2]
        _ = F * (cos alpha - k * l) := by
          dsimp only [X, Y, D, F]
          linear_combination k * l * sin_sq_add_cos_sq alpha
    · change -(-(X * (l * u) + (k * u) * Y)) = F * u + 0 * (cos alpha - k * l)
      rw [neg_neg, zero_mul, add_zero]
      exact him
  have hzk0 : zk ≠ 0 := by intro hh; simp [hh] at hzk
  have hzl0 : zl ≠ 0 := by intro hh; simp [hh] at hzl
  have hkarg0 : 0 ≤ zk.arg := Complex.arg_nonneg_iff.mpr hzk.le
  have hlarg0 : 0 ≤ zl.arg := Complex.arg_nonneg_iff.mpr hzl.le
  have hkargp : zk.arg < π := Complex.arg_lt_pi_iff.mpr (Or.inr hzk.ne')
  have hlargp : zl.arg < π := Complex.arg_lt_pi_iff.mpr (Or.inr hzl.ne')
  have hsum_sin : sin (zk.arg + zl.arg) = (zk * zl).im / (‖zk‖ * ‖zl‖) := by
    rw [sin_add, Complex.sin_arg, Complex.cos_arg hzl0, Complex.cos_arg hzk0, Complex.sin_arg]
    simp only [Complex.mul_im]
    field_simp
    <;> ring
  have hsum_sin_pos : 0 < sin (zk.arg + zl.arg) := by
    rw [hsum_sin]
    exact div_pos hpim (mul_pos (norm_pos_iff.mpr hzk0) (norm_pos_iff.mpr hzl0))
  have hsum_lt : zk.arg + zl.arg < π := by
    by_contra hh
    have hnn : 0 ≤ sin (zk.arg + zl.arg - π) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [sin_sub_pi] at hnn
    linarith
  have hmul : (zk * zl).arg = zk.arg + zl.arg :=
    Complex.arg_mul hzk0 hzl0 ⟨by linarith [pi_pos], hsum_lt.le⟩
  have hnpi : (zk * zl).arg ≠ π :=
    ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inr hpim.ne'))
  have hbranch : Complex.arg (-(starRingEnd ℂ) (zk * zl)) = π - zk.arg - zl.arg := by
    rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg, Complex.arg_conj, if_neg hnpi, hmul]
    · ring
    · change -(zk * zl).im < 0
      exact neg_neg_of_pos hpim
  rw [heq, Complex.arg_real_mul _ hF] at hbranch
  have hnotboth : ¬ (X < 0 ∧ Y < 0) := by
    intro ⟨hx, hy⟩
    have hxneg : l * X < 0 := mul_neg_of_pos_of_neg hl0 hx
    have hyneg : k * Y < 0 := mul_neg_of_pos_of_neg hk0 hy
    have hsum : l * X + k * Y = F := by dsimp only [X, Y, F]; ring
    linarith only [hxneg, hyneg, hsum, hF]
  refine ⟨hargk, hargl, ?_⟩
  rw [hbranch, hbetak, hbetal]
  by_cases hx : X < 0
  · have hy : ¬ Y < 0 := fun hy => hnotboth ⟨hx, hy⟩
    rw [if_pos hx, if_neg hy, if_pos hx]
    ring
  · by_cases hy : Y < 0
    · rw [if_neg hx, if_pos hy, if_neg hx, if_pos hy]
      ring
    · rw [if_neg hx, if_neg hy, if_neg hx, if_neg hy]
