import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem proof_SolidGeom_beta_inscribed (R x y z : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hs : x + y + z = π) :
    Complex.arg ⟨(2 * R * sin x) * (4 * R ^ 2 * sin z ^ 2 + 4 * R ^ 2 * sin y ^ 2 - 4 * R ^ 2 * sin x ^ 2),
        2 * (2 * √(1 - R ^ 2) * R ^ 2 * (sin (2 * x) + sin (2 * y) + sin (2 * z)))⟩ =
      Complex.arg ⟨R * cos x, √(1 - R ^ 2)⟩ := by
  have sx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith)
  have sy : 0 < sin y := sin_pos_of_pos_of_lt_pi hy (by linarith)
  have sz : 0 < sin z := sin_pos_of_pos_of_lt_pi hz (by linarith)
  have htri :
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
  obtain ⟨hc, hd⟩ := htri
  let k : ℝ := 16 * R^2 * sin x * sin y * sin z
  have hk : 0 < k := by dsimp [k]; positivity
  have heq : (⟨(2 * R * sin x) * (4 * R ^ 2 * sin z ^ 2 + 4 * R ^ 2 * sin y ^ 2 - 4 * R ^ 2 * sin x ^ 2),
        2 * (2 * √(1 - R ^ 2) * R ^ 2 * (sin (2 * x) + sin (2 * y) + sin (2 * z)))⟩ : ℂ) =
      (k : ℂ) * ⟨R*cos x, √(1-R^2)⟩ := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      dsimp [k]
      linear_combination 8*R^3*sin x*hc
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      dsimp [k]
      rw [hd]
      ring
  rw [heq]
  exact Complex.arg_real_mul _ hk
