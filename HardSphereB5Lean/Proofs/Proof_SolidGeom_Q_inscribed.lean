import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem proof_SolidGeom_Q_inscribed (R x y z : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = π) :
    √(4 * (4 * R ^ 2 * sin z ^ 2) * (4 * R ^ 2 * sin y ^ 2)
        - (4 * R ^ 2 * sin z ^ 2 + 4 * R ^ 2 * sin y ^ 2 - 4 * R ^ 2 * sin x ^ 2) ^ 2
        - (4 * R ^ 2 * sin z ^ 2) * (4 * R ^ 2 * sin y ^ 2) * (4 * R ^ 2 * sin x ^ 2)) =
      2 * √(1 - R ^ 2) * R ^ 2 * (sin (2 * x) + sin (2 * y) + sin (2 * z)) := by
  have sx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith)
  have sy : 0 < sin y := sin_pos_of_pos_of_lt_pi hy (by linarith)
  have sz : 0 < sin z := sin_pos_of_pos_of_lt_pi hz (by linarith)
  have hr : 0 < 1 - R ^ 2 := by nlinarith
  have hh : 0 < √(1-R^2) := sqrt_pos.2 hr
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
  have hl : 4*R^2*sin z^2+4*R^2*sin y^2-4*R^2*sin x^2 =
      8*R^2*sin y*sin z*cos x := by
    linear_combination 4*R^2*hc
  have hrad : 4 * (4 * R ^ 2 * sin z ^ 2) * (4 * R ^ 2 * sin y ^ 2)
        - (4 * R ^ 2 * sin z ^ 2 + 4 * R ^ 2 * sin y ^ 2 - 4 * R ^ 2 * sin x ^ 2) ^ 2
        - (4 * R ^ 2 * sin z ^ 2) * (4 * R ^ 2 * sin y ^ 2) * (4 * R ^ 2 * sin x ^ 2) =
        64*R^4*sin x^2*sin y^2*sin z^2*(1-R^2) := by
    rw [hl]
    linear_combination -(64*R^4*sin y^2*sin z^2) * (sin_sq_add_cos_sq x)
  rw [hd]
  apply (sqrt_eq_iff_eq_sq (by rw [hrad]; positivity) (by positivity)).2
  rw [hrad]
  symm
  calc
    (2 * √(1-R^2) * R^2 * (4*sin x*sin y*sin z))^2 =
        64 * (√(1-R^2))^2 * R^4*sin x^2*sin y^2*sin z^2 := by ring
    _ = _ := by rw [sq_sqrt hr.le]; ring
