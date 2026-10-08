import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
private theorem arg_upper (x y : ℝ) (hy : 0 < y) : Complex.arg ⟨x,y⟩ = Real.pi / 2 - Real.arctan (x / y) := by
  let z : ℂ := ⟨x,y⟩
  have hnonneg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (le_of_lt hy)
  have hne : z.arg ≠ 0 := by
    intro hz
    have := (Complex.arg_eq_zero_iff.mp hz).2
    exact hy.ne' this
  have hpos : 0 < z.arg := lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hlt : z.arg < π := Complex.arg_lt_pi_iff.mpr (Or.inr hy.ne')
  have ht := Real.arctan_tan (x := π / 2 - z.arg) (by linarith) (by linarith)
  rw [Real.tan_pi_div_two_sub, Complex.tan_arg] at ht
  simp only [inv_div] at ht
  change arctan (x / y) = π / 2 - z.arg at ht
  change z.arg = π / 2 - arctan (x / y)
  linarith
private theorem arg_deriv {f : ℝ → ℂ} {v : ℂ} {t : ℝ} (hf : HasDerivAt f v t) (ht : f t ∈ Complex.slitPlane) : HasDerivAt (fun s => Complex.arg (f s)) (v / f t).im t := by
  have hl := (Complex.hasDerivAt_log ht).complexToReal_fderiv.comp_hasDerivAt t hf
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hl
  simpa [Function.comp_def, Complex.log_im, div_eq_mul_inv, mul_comm] using hi
theorem proof_SolidGeom_integral_vertex_sector (R α : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hα0 : 0 ≤ α) (hα : α < π) :
    ∫ t in (0 : ℝ)..α, (2 / 3 * √(1 - R ^ 2) ^ 3 + (R * cos t) ^ 2 * √(1 - R ^ 2)
        - R * cos t * (√(1 - R ^ 2) ^ 2 + (R * cos t) ^ 2) * (π / 2 - arctan (R * cos t / √(1 - R ^ 2)))) =
      2 / 3 * Complex.arg ⟨cos α, √(1 - R ^ 2) * sin α⟩
        - (2 * R * sin α - (2 * R * sin α) ^ 3 / 12) / 2 * Complex.arg ⟨R * cos α, √(1 - R ^ 2)⟩
        + √(1 - R ^ 2) * R ^ 2 * sin (2 * α) / 6 := by
  let h : ℝ := √(1-R^2)
  have hh : 0 < h := by dsimp [h]; apply Real.sqrt_pos.2; nlinarith
  have hsq : h^2 = 1-R^2 := Real.sq_sqrt (by nlinarith)
  have hd1 : ∀ t : ℝ, 0 ≤ t → t < π → HasDerivAt
      (fun s => Complex.arg ⟨cos s,h*sin s⟩)
      (h/(cos t^2+h^2*sin t^2)) t := by
    intro t h0 ht
    have hs : (⟨cos t,h*sin t⟩ : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      rcases eq_or_lt_of_le h0 with rfl | h0
      · simp
      · exact Or.inr (mul_pos hh (sin_pos_of_pos_of_lt_pi h0 ht)).ne'
    have hd : HasDerivAt (fun s : ℝ => (⟨cos s, h*sin s⟩ : ℂ))
        ⟨-sin t,h*cos t⟩ t := by
      simpa only [Complex.mk_eq_add_mul_I, Pi.add_apply, Complex.ofReal_neg] using
        (hasDerivAt_cos t).ofReal_comp.fun_add
          (((hasDerivAt_sin t).const_mul h).ofReal_comp.mul_const Complex.I)
    convert! arg_deriv hd hs using 1
    simp only [Complex.div_im, Complex.normSq_mk]
    have dn : cos t * cos t + h * sin t * (h * sin t) ≠ 0 := by
      nlinarith [sin_sq_add_cos_sq t, sq_pos_of_pos hh, sq_nonneg (h*cos t)]
    have de : cos t ^ 2 + h ^ 2 * sin t ^ 2 = cos t * cos t + h * sin t * (h * sin t) := by ring
    rw [de]
    have trig : cos t ^ 2 + sin t ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq t]
    calc
      _ = h * (cos t ^ 2 + sin t ^ 2) / (cos t * cos t + h*sin t*(h*sin t)) := by rw [trig]; ring
      _ = _ := by ring
  have hd2 : ∀ t : ℝ, HasDerivAt
      (fun s => Complex.arg ⟨R*cos s,h⟩)
      (R*h*sin t/(h^2+R^2*cos t^2)) t := by
    intro t
    have hs : (⟨R*cos t,h⟩ : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr hh.ne')
    have hd : HasDerivAt (fun s : ℝ => (⟨R*cos s,h⟩ : ℂ))
        ⟨-R*sin t,0⟩ t := by
      simpa [Complex.mk_eq_add_mul_I, neg_mul, mul_neg] using
        ((hasDerivAt_cos t).const_mul R).ofReal_comp.add_const ((h : ℂ)*Complex.I)
    convert! arg_deriv hd hs using 1
    simp only [Complex.div_im, Complex.normSq_mk]
    ring
  let F : ℝ → ℝ := fun t =>
    2/3 * Complex.arg ⟨cos t,h*sin t⟩
      - (2*R*sin t-(2*R*sin t)^3/12)/2 * Complex.arg ⟨R*cos t,h⟩
      + h*R^2*sin (2*t)/6
  let g : ℝ → ℝ := fun t => 2/3*h^3+(R*cos t)^2*h
    - R*cos t*(h^2+(R*cos t)^2)*(π/2-arctan (R*cos t/h))
  have hder : ∀ t ∈ Set.Icc (0:ℝ) α, HasDerivAt F (g t) t := by
    intro t ht
    have d1 := hd1 t ht.1 (lt_of_le_of_lt ht.2 hα)
    have d2 := hd2 t
    have dc : HasDerivAt (fun s : ℝ => (2*R*sin s-(2*R*sin s)^3/12)/2)
        (R*cos t*(1-R^2*sin t^2)) t := by
      convert! (((hasDerivAt_sin t).const_mul (2*R)).fun_sub
        ((((hasDerivAt_sin t).const_mul (2*R)).pow 3).div_const 12)).div_const 2 using 1 <;> ring
    have da : HasDerivAt (fun s : ℝ => h*R^2*sin (2*s)/6)
        (h*R^2*(cos (2*t)*2)/6) t := by
      convert! (((hasDerivAt_id t).const_mul 2).sin.const_mul (h*R^2)).div_const 6 using 1 <;> simp <;> ring
    convert! ((d1.const_mul (2/3:ℝ)).fun_sub (dc.mul d2)).fun_add da using 1
    dsimp [g]
    rw [arg_upper (R*cos t) h hh, cos_two_mul]
    have trig := sin_sq_add_cos_sq t
    have dp : 0 < h^2+R^2*cos t^2 := by nlinarith [sq_pos_of_pos hh, sq_nonneg (R*cos t)]
    have de : cos t^2+h^2*sin t^2 = h^2+R^2*cos t^2 := by nlinarith [hsq,trig]
    rw [de]
    field_simp [dp.ne']
    grind
  have hint : IntervalIntegrable g volume 0 α := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hder t (by simpa [Set.uIcc_of_le hα0] using ht)) hint
  have hz : F 0 = 0 := by
    dsimp [F]
    simp only [sin_zero, cos_zero, mul_zero, zero_pow, zero_div, sub_zero, zero_mul, add_zero]
    have ze : (⟨(1:ℝ),0⟩ : ℂ) = 1 := by rfl
    rw [ze,Complex.arg_one,mul_zero]
    ring
  change (∫ t in (0:ℝ)..α, g t) = F α
  rw [he,hz,sub_zero]
