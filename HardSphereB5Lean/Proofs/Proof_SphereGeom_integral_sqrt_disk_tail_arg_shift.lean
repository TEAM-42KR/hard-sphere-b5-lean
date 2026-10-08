import Mathlib
set_option autoImplicit false

open MeasureTheory intervalIntegral

private theorem semicircle_tail_aux (r a : ℝ) (hr : 0 < r) (ha0 : -r < a) (ha1 : a < r) :
    (∫ t in a..r, Real.sqrt (r ^ 2 - t ^ 2)) =
      (r ^ 2 / 2) * Real.arccos (a / r) - (a / 2) * Real.sqrt (r ^ 2 - a ^ 2) := by
  have ha0' : -1 ≤ a / r := by
    rw [le_div_iff₀ hr]
    linarith
  have ha1' : a / r ≤ 1 := by
    rw [div_le_iff₀ hr]
    linarith
  let θ := Real.arcsin (a / r)
  have hlo : -(Real.pi / 2) ≤ θ := (Real.arcsin_mem_Icc (a / r)).1
  have hhi : θ ≤ Real.pi / 2 := (Real.arcsin_mem_Icc (a / r)).2
  have hsin : Real.sin θ = a / r := Real.sin_arcsin ha0' ha1'
  have hend : r * Real.sin θ = a := by
    rw [hsin]
    field_simp
  have hroot (t : ℝ) (ht0 : -(Real.pi / 2) ≤ t) (ht1 : t ≤ Real.pi / 2) :
      Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2) = r * Real.cos t := by
    have he : r ^ 2 - (r * Real.sin t) ^ 2 = r ^ 2 * (1 - Real.sin t ^ 2) := by ring
    rw [he, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le,
      ← Real.cos_eq_sqrt_one_sub_sin_sq ht0 ht1]
  have hroota : Real.sqrt (r ^ 2 - a ^ 2) = r * Real.cos θ := by
    simpa only [hend] using hroot θ hlo hhi
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := θ) (b := Real.pi / 2)
    (f := fun t : ℝ => r * Real.sin t) (f' := fun t : ℝ => r * Real.cos t)
    (g := fun t : ℝ => Real.sqrt (r ^ 2 - t ^ 2))
    (fun t _ => (Real.hasDerivAt_sin t).const_mul r)
    (by fun_prop) (by fun_prop)
  have hsub' : (∫ t in a..r, Real.sqrt (r ^ 2 - t ^ 2)) =
      ∫ t in θ..Real.pi / 2,
        Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2) * (r * Real.cos t) := by
    simpa only [Function.comp_apply, hend, Real.sin_pi_div_two, mul_one] using hsub.symm
  calc
    (∫ t in a..r, Real.sqrt (r ^ 2 - t ^ 2)) =
        ∫ t in θ..Real.pi / 2, r ^ 2 * Real.cos t ^ 2 := by
      rw [hsub']
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [Set.uIcc_of_le hhi] at ht
      rw [hroot t (hlo.trans ht.1) ht.2]
      ring
    _ = r ^ 2 * ((Real.cos (Real.pi / 2) * Real.sin (Real.pi / 2) -
          Real.cos θ * Real.sin θ + Real.pi / 2 - θ) / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_cos_sq]
    _ = (r ^ 2 / 2) * Real.arccos (a / r) -
          (a / 2) * Real.sqrt (r ^ 2 - a ^ 2) := by
      rw [Real.cos_pi_div_two, Real.sin_pi_div_two, hsin, hroota,
        Real.arccos_eq_pi_div_two_sub_arcsin]
      dsimp only [θ]
      field_simp
      <;> ring

private theorem g3m_tail_extended (r a b : ℝ) (hr : 0 < r) (ha0 : -r < a) (ha1 : a < r) (hb : r ≤ b) :
    (∫ t in a..b, Real.sqrt (r ^ 2 - t ^ 2)) =
      (r ^ 2 / 2) * Real.arccos (a / r) - (a / 2) * Real.sqrt (r ^ 2 - a ^ 2) := by
  have hc : Continuous (fun t : ℝ => Real.sqrt (r ^ 2 - t ^ 2)) := by fun_prop
  have hz : (∫ t in r..b, Real.sqrt (r ^ 2 - t ^ 2)) = 0 := by
    calc
      _ = ∫ t in r..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hb] at ht
        apply Real.sqrt_eq_zero_of_nonpos
        nlinarith [mul_nonneg hr.le (sub_nonneg.mpr ht.1), sq_nonneg (t - r)]
      _ = 0 := by simp
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable a r) (hc.intervalIntegrable r b)
  rw [hz, add_zero] at hadj
  rw [← hadj]
  exact semicircle_tail_aux r a hr ha0 ha1

open MeasureTheory Real

theorem proof_SphereGeom_integral_sqrt_disk_tail_arg_shift (r d h b : ℝ) (hr : 0 < r) (hh0 : -r < h - d) (hh1 : h - d < r) (hb : d + r ≤ b) :
 (∫ t in h..b, Real.sqrt (r ^ 2 - (t - d) ^ 2)) = (r ^ 2 / 2) * Complex.arg ⟨h-d, Real.sqrt (r ^ 2 - (h - d) ^ 2)⟩ - ((h - d) / 2) * Real.sqrt (r ^ 2 - (h - d) ^ 2) := by
  have hp : 0 < r^2-(h-d)^2 := by nlinarith
  let z : ℂ := ⟨h-d,sqrt (r^2-(h-d)^2)⟩
  have hz : ‖z‖=r := by
    have hh : ‖z‖^2=r^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      dsimp [z]
      nlinarith [Real.sq_sqrt hp.le]
    nlinarith [norm_nonneg z]
  have ha : Complex.arg z = arccos ((h-d)/r) := by
    rw [Complex.arg_of_im_pos (by dsimp [z]; positivity),hz]
  have hshift := intervalIntegral.integral_comp_sub_right (a:=h) (b:=b)
    (fun t : ℝ => sqrt (r^2-t^2)) d
  rw [hshift, g3m_tail_extended r (h-d) (b-d) hr hh0 hh1 (by linarith)]
  rw [← ha]
