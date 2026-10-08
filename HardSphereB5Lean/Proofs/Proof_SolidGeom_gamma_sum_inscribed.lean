import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

private theorem branch_identity (a b : ℂ) (ha : 0 < a.im) (hb : 0 < b.im)
    (hab : 0 < (a * b).im) :
    Complex.arg (-(starRingEnd ℂ) (a * b)) = Real.pi - Complex.arg a - Complex.arg b := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hap : 0 ≤ a.arg := Complex.arg_nonneg_iff.mpr ha.le
  have hbp : 0 ≤ b.arg := Complex.arg_nonneg_iff.mpr hb.le
  have hau : a.arg < π := Complex.arg_lt_pi_iff.mpr (Or.inr ha.ne')
  have hbu : b.arg < π := Complex.arg_lt_pi_iff.mpr (Or.inr hb.ne')
  have hs : sin (a.arg + b.arg) = (a * b).im / (‖a‖ * ‖b‖) := by
    rw [sin_add, Complex.sin_arg, Complex.cos_arg hb0, Complex.cos_arg ha0, Complex.sin_arg]
    simp only [Complex.mul_im]
    field_simp
    <;> ring
  have hspos : 0 < sin (a.arg + b.arg) := by
    rw [hs]
    exact div_pos hab (mul_pos (norm_pos_iff.mpr ha0) (norm_pos_iff.mpr hb0))
  have hsum : a.arg + b.arg < π := by
    by_contra hh
    have hnn : 0 ≤ sin (a.arg + b.arg - π) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [sin_sub_pi] at hnn
    linarith
  have hmul : (a * b).arg = a.arg + b.arg :=
    Complex.arg_mul ha0 hb0 ⟨by linarith [pi_pos], hsum.le⟩
  have hprod : (a * b).arg ≠ π := ne_of_lt
    (Complex.arg_lt_pi_iff.mpr (Or.inr hab.ne'))
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg, Complex.arg_conj, if_neg hprod, hmul]
  · ring
  · change -(a * b).im < 0
    exact neg_neg_of_pos hab

private theorem vertex_identity (R x y z : ℝ) (hR0 : 0 < R) (hR1 : R < 1)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hs : x + y + z = π) :
    Complex.arg ⟨cos x - R ^ 2 * sin y * sin z, √(1 - R ^ 2) * sin x⟩ =
      π - Complex.arg ⟨cos y, √(1 - R ^ 2) * sin y⟩
        - Complex.arg ⟨cos z, √(1 - R ^ 2) * sin z⟩ := by
  let h : ℝ := √(1 - R ^ 2)
  have hq : 0 < 1 - R ^ 2 := by nlinarith
  have hp : 0 < h := Real.sqrt_pos.mpr hq
  have hh : h ^ 2 = 1 - R ^ 2 := Real.sq_sqrt hq.le
  have sx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith)
  have sy : 0 < sin y := sin_pos_of_pos_of_lt_pi hy (by linarith)
  have sz : 0 < sin z := sin_pos_of_pos_of_lt_pi hz (by linarith)
  have hyz : y + z = π - x := by linarith
  have hsin : sin (y + z) = sin x := by rw [hyz, sin_pi_sub]
  have hcos : cos (y + z) = -cos x := by rw [hyz, cos_pi_sub]
  let a : ℂ := ⟨cos y, h * sin y⟩
  let b : ℂ := ⟨cos z, h * sin z⟩
  have hae : 0 < a.im := mul_pos hp sy
  have hbe : 0 < b.im := mul_pos hp sz
  have hime : (a * b).im = h * sin x := by
    change cos y * (h * sin z) + (h * sin y) * cos z = h * sin x
    calc
      _ = h * sin (y + z) := by rw [sin_add]; ring
      _ = h * sin x := by rw [hsin]
  have hpab : 0 < (a * b).im := by rw [hime]; exact mul_pos hp sx
  have heq : -(starRingEnd ℂ) (a * b) =
      (⟨cos x - R ^ 2 * sin y * sin z, h * sin x⟩ : ℂ) := by
    apply Complex.ext
    · change -(cos y * cos z - (h * sin y) * (h * sin z)) =
        cos x - R ^ 2 * sin y * sin z
      calc
        _ = -(cos y * cos z - sin y * sin z) - R ^ 2 * sin y * sin z := by
          linear_combination (sin y * sin z) * hh
        _ = cos x - R ^ 2 * sin y * sin z := by rw [← cos_add, hcos]; ring
    · simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hime
  have ht := branch_identity a b hae hbe hpab
  rw [heq] at ht
  exact ht

private theorem triangle_identity (x y z : ℝ) (hs : x+y+z=Real.pi) :
 (sin y ^ 2 + sin z ^ 2 - sin x ^ 2 = 2*sin y*sin z*cos x) ∧
 (sin (2*x)+sin (2*y)+sin (2*z)=4*sin x*sin y*sin z) := by
 have he : x = Real.pi - (y+z) := by linarith
 have sx : sin x = sin y*cos z+cos y*sin z := by rw [he, sin_pi_sub, sin_add]
 have cx : cos x = -(cos y*cos z-sin y*sin z) := by rw [he, cos_pi_sub, cos_add]
 have hy := sin_sq_add_cos_sq y
 have hz := sin_sq_add_cos_sq z
 constructor
 · rw [sx, cx]
   linear_combination -(sin y)^2 * hz - (sin z)^2 * hy
 · rw [sin_two_mul, sin_two_mul, sin_two_mul, sx, cx]
   linear_combination -2*sin y*cos y*hz - 2*sin z*cos z*hy

theorem proof_SolidGeom_gamma_sum_inscribed (R x y z : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hs : x + y + z = π) :
    let S : ℝ → ℝ := fun t => 4 * R ^ 2 * sin t ^ 2
    let q := 2 * (2 * √(1 - R ^ 2) * R ^ 2 * (sin (2 * x) + sin (2 * y) + sin (2 * z)))
    Complex.arg ⟨2 * (S z + S y - S x) - S z * S y, q⟩
      + Complex.arg ⟨2 * (S x + S z - S y) - S x * S z, q⟩
      + Complex.arg ⟨2 * (S y + S x - S z) - S y * S x, q⟩ =
      3 * π - 2 * (Complex.arg ⟨cos x, √(1 - R ^ 2) * sin x⟩ + Complex.arg ⟨cos y, √(1 - R ^ 2) * sin y⟩
        + Complex.arg ⟨cos z, √(1 - R ^ 2) * sin z⟩) := by
  dsimp only
  let h : ℝ := √(1 - R ^ 2)
  have hgamma (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (habc : a + b + c = π) :
      Complex.arg ⟨2 * (4 * R ^ 2 * sin c ^ 2 + 4 * R ^ 2 * sin b ^ 2 - 4 * R ^ 2 * sin a ^ 2)
          - (4 * R ^ 2 * sin c ^ 2) * (4 * R ^ 2 * sin b ^ 2),
        2 * (2 * h * R ^ 2 * (sin (2 * a) + sin (2 * b) + sin (2 * c)))⟩ =
      π - Complex.arg ⟨cos b, h * sin b⟩ - Complex.arg ⟨cos c, h * sin c⟩ := by
    have sb : 0 < sin b := sin_pos_of_pos_of_lt_pi hb (by linarith)
    have sc : 0 < sin c := sin_pos_of_pos_of_lt_pi hc (by linarith)
    have tt := triangle_identity a b c habc
    let r : ℝ := 16 * R ^ 2 * sin b * sin c
    have hr : 0 < r := by dsimp only [r]; positivity
    have he : (⟨2 * (4 * R ^ 2 * sin c ^ 2 + 4 * R ^ 2 * sin b ^ 2 - 4 * R ^ 2 * sin a ^ 2)
          - (4 * R ^ 2 * sin c ^ 2) * (4 * R ^ 2 * sin b ^ 2),
        2 * (2 * h * R ^ 2 * (sin (2 * a) + sin (2 * b) + sin (2 * c)))⟩ : ℂ) =
        (r : ℂ) * ⟨cos a - R ^ 2 * sin b * sin c, h * sin a⟩ := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        dsimp only [r]
        linear_combination (8 * R ^ 2) * tt.1
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        rw [tt.2]
        dsimp only [r]
        ring
    rw [he, Complex.arg_real_mul _ hr]
    exact vertex_identity R a b c hR0 hR1 ha hb hc habc
  have gx := hgamma x y z hx hy hz hs
  have gy := hgamma y z x hy hz hx (by linarith)
  have gz := hgamma z x y hz hx hy (by linarith)
  have hyq : sin (2 * y) + sin (2 * z) + sin (2 * x) =
      sin (2 * x) + sin (2 * y) + sin (2 * z) := by ring
  have hzq : sin (2 * z) + sin (2 * x) + sin (2 * y) =
      sin (2 * x) + sin (2 * y) + sin (2 * z) := by ring
  rw [hyq] at gy
  rw [hzq] at gz
  dsimp only [h] at gx gy gz
  linarith [gx, gy, gz]
