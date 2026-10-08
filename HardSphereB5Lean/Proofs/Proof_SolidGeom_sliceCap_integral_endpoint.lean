import Mathlib
set_option autoImplicit false

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

open Filter Set
open scoped Topology

theorem proof_SolidGeom_sliceCap_integral_endpoint (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    (∫ z in (0 : ℝ)..Real.sqrt (1 - k ^ 2), Real.arccos (k / Real.sqrt (1 - z ^ 2))) =
      Real.pi * (1 - k) / 2 := by
  let c := Real.sqrt (1 - k ^ 2)
  let f : ℝ → ℝ := fun z => Real.arccos (k / Real.sqrt (1 - z ^ 2))
  let F : ℝ → ℝ := fun z => z * f z +
    Real.arctan (k * z / Real.sqrt (1 - k ^ 2 - z ^ 2)) -
    k * Real.arcsin (z / c)
  have hC : 0 < 1 - k ^ 2 := by
    have := (sq_lt_sq₀ (le_of_lt hk0) (by norm_num : (0 : ℝ) ≤ 1)).2 hk1
    nlinarith
  have hc : 0 < c := Real.sqrt_pos.2 hC
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hcsq : c ^ 2 = 1 - k ^ 2 := Real.sq_sqrt hC.le
  have hrootc : Real.sqrt (1 - c ^ 2) = k := by
    rw [show 1 - c ^ 2 = k ^ 2 by nlinarith [hcsq], Real.sqrt_sq hk0.le]
  have hinside (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) c) : x ^ 2 < 1 - k ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) (add_pos hc hx.1)]
  have hfAt (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) c) : ContinuousAt f x := by
    rw [uIcc_of_le hc.le] at hx
    have hx2 : x ^ 2 ≤ c ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hc.le hx.1)]
    have hroot : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 (by
      nlinarith [sq_pos_of_pos hk0])
    exact Real.continuous_arccos.continuousAt.comp
      (continuousAt_const.div ((continuousAt_const.sub (continuousAt_id.pow 2)).sqrt) hroot)
  have hfc : ContinuousAt f c := hfAt c (by simp)
  have hcont : ContinuousOn f (uIcc (0 : ℝ) c) := fun x hx => (hfAt x hx).continuousWithinAt
  have hint : IntervalIntegrable f volume (0 : ℝ) c := hcont.intervalIntegrable
  have hm : Measurable f := by dsimp [f]; fun_prop
  have hIcont : ContinuousAt (fun t : ℝ => ∫ z in (0 : ℝ)..t, f z) c :=
    (intervalIntegral.integral_hasDerivAt_right hint
      hm.stronglyMeasurable.stronglyMeasurableAtFilter hfc).continuousAt
  have hid : Tendsto (fun z : ℝ => z) (𝓝[<] c) (𝓝 c) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hcos : Tendsto (fun z : ℝ => z * f z) (𝓝[<] c) (𝓝 0) := by
    have ht := hid.mul (hfc.tendsto.mono_left nhdsWithin_le_nhds)
    simpa [f, hrootc, div_self (ne_of_gt hk0)] using ht
  have hsin : Tendsto (fun z : ℝ => k * Real.arcsin (z / c))
      (𝓝[<] c) (𝓝 (k * (Real.pi / 2))) := by
    have ht := Real.continuous_arcsin.continuousAt.tendsto.comp
      (hid.div tendsto_const_nhds hc0)
    simpa [div_self hc0] using ht.const_mul k
  have hden : Tendsto (fun z : ℝ => Real.sqrt (1 - k ^ 2 - z ^ 2))
      (𝓝[<] c) (𝓝 0) := by
    have hct : Continuous (fun z : ℝ => Real.sqrt (1 - k ^ 2 - z ^ 2)) := by fun_prop
    have ht : Tendsto (fun z : ℝ => Real.sqrt (1 - k ^ 2 - z ^ 2))
        (𝓝[<] c) (𝓝 (Real.sqrt (1 - k ^ 2 - c ^ 2))) :=
      (hct.continuousAt (x := c)).tendsto.mono_left nhdsWithin_le_nhds
    simpa [show 1 - k ^ 2 - c ^ 2 = 0 by linarith [hcsq]] using ht
  have hdenpos : ∀ᶠ z in 𝓝[<] c, 0 < Real.sqrt (1 - k ^ 2 - z ^ 2) := by
    filter_upwards [Ioo_mem_nhdsLT hc] with z hz
    exact Real.sqrt_pos.2 (by linarith [hinside z hz])
  have hdenGT : Tendsto (fun z : ℝ => Real.sqrt (1 - k ^ 2 - z ^ 2))
      (𝓝[<] c) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hden, hdenpos⟩
  have htop : Tendsto (fun z : ℝ => k * z / Real.sqrt (1 - k ^ 2 - z ^ 2))
      (𝓝[<] c) atTop := by
    convert! (tendsto_const_nhds.mul hid).pos_mul_atTop (mul_pos hk0 hc)
      hdenGT.inv_tendsto_nhdsGT_zero using 1 <;> simp only [div_eq_mul_inv, Pi.inv_apply]
  have htan : Tendsto (fun z : ℝ => Real.arctan (k * z / Real.sqrt (1 - k ^ 2 - z ^ 2)))
      (𝓝[<] c) (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp htop
  have hF : Tendsto F (𝓝[<] c) (𝓝 (Real.pi * (1 - k) / 2)) := by
    convert! (hcos.add htan).sub hsin using 1 <;> ring
  have hEq : (fun t : ℝ => ∫ z in (0 : ℝ)..t, f z) =ᶠ[𝓝[<] c] F := by
    filter_upwards [Ioo_mem_nhdsLT hc] with t ht
    exact sliceCap_integral_aux k t hk0 hk1 ht.1.le (hinside t ht)
  have hIlim : Tendsto (fun t : ℝ => ∫ z in (0 : ℝ)..t, f z)
      (𝓝[<] c) (𝓝 (Real.pi * (1 - k) / 2)) := hF.congr' hEq.symm
  exact tendsto_nhds_unique (hIcont.tendsto.mono_left nhdsWithin_le_nhds) hIlim
