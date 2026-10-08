import Mathlib
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_threshold
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_continuous
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_inner_integral
set_option autoImplicit false

open MeasureTheory Real Filter Set
open scoped Topology
set_option maxHeartbeats 1000000

theorem proof_SolidGeom_twoCapSlice_integral_threshold (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) :
    let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
    let h := sqrt D / sin alpha
    let Ck := sqrt (1 - k ^ 2)
    let Cl := sqrt (1 - l ^ 2)
    let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
    let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
    let Tk := if l - k * cos alpha = 0 then π / 2
      else arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2))
    let Tl := if k - l * cos alpha = 0 then π / 2
      else arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2))
    (∫ z in (0 : ℝ)..h, max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha)))) =
      h * (f h + g h - alpha) + Tk + Tl -
        k * arcsin (h / Ck) - l * arcsin (h / Cl) := by
  dsimp only
  let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
  let h := sqrt D / sin alpha
  let Ck := sqrt (1 - k ^ 2)
  let Cl := sqrt (1 - l ^ 2)
  let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
  let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
  let E := fun z : ℝ => max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha)))
  let Xk := l - k * cos alpha
  let Xl := k - l * cos alpha
  let Tk := if Xk = 0 then π / 2 else arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2))
  let Tl := if Xl = 0 then π / 2 else arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2))
  let F := fun t : ℝ => t * (f t + g t - alpha) +
    arctan (k * t / sqrt (1 - k ^ 2 - t ^ 2)) +
    arctan (l * t / sqrt (1 - l ^ 2 - t ^ 2)) -
    k * arcsin (t / Ck) - l * arcsin (t / Cl)
  change (∫ z in (0 : ℝ)..h, E z) =
    h * (f h + g h - alpha) + Tk + Tl - k * arcsin (h / Ck) - l * arcsin (h / Cl)
  have hs : 0 < sin alpha := sin_pos_of_pos_of_lt_pi ha0 hap
  have hthreshold := SolidGeom.twoCapSlice_threshold k l alpha hk0 hk1 hl0 hl1 ha0 hap hD
  change 0 < h ∧ h ≤ min Ck Cl ∧
    1 - k ^ 2 - h ^ 2 = Xk ^ 2 / sin alpha ^ 2 ∧
    1 - l ^ 2 - h ^ 2 = Xl ^ 2 / sin alpha ^ 2 at hthreshold
  rcases hthreshold with ⟨hh, hb, hrk, hrl⟩
  have hCk : 0 < 1 - k ^ 2 := by nlinarith [mul_pos hk0 (sub_pos.mpr hk1)]
  have hCl : 0 < 1 - l ^ 2 := by nlinarith [mul_pos hl0 (sub_pos.mpr hl1)]
  have hsq : h ^ 2 = D / sin alpha ^ 2 := by
    dsimp [h]
    rw [div_pow, sq_sqrt hD.le]
  have hinside (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) h) : t ^ 2 < h ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr ht.2) (add_pos hh ht.1)]
  have hid : Tendsto (fun t : ℝ => t) (𝓝[<] h) (𝓝 h) :=
    tendsto_id'.2 nhdsWithin_le_nhds

  have hatan (q X : ℝ) (hq : 0 < q)
      (hr : 1 - q ^ 2 - h ^ 2 = X ^ 2 / sin alpha ^ 2) :
      Tendsto (fun t : ℝ => arctan (q * t / sqrt (1 - q ^ 2 - t ^ 2)))
        (𝓝[<] h)
        (𝓝 (if X = 0 then π / 2 else arctan (q * h / sqrt (1 - q ^ 2 - h ^ 2)))) := by
    have hd : Tendsto (fun t : ℝ => sqrt (1 - q ^ 2 - t ^ 2))
        (𝓝[<] h) (𝓝 (sqrt (1 - q ^ 2 - h ^ 2))) :=
      ((continuousAt_const.sub (continuousAt_id.pow 2)).sqrt).tendsto.mono_left
        nhdsWithin_le_nhds
    by_cases hx : X = 0
    · simp only [hx, if_true]
      have hr0 : 1 - q ^ 2 - h ^ 2 = 0 := by simpa [hx] using hr
      have hdz : Tendsto (fun t : ℝ => sqrt (1 - q ^ 2 - t ^ 2))
          (𝓝[<] h) (𝓝 (0 : ℝ)) := by simpa [hr0] using hd
      have hdpos : ∀ᶠ t : ℝ in 𝓝[<] h, 0 < sqrt (1 - q ^ 2 - t ^ 2) := by
        filter_upwards [Ioo_mem_nhdsLT hh] with t ht
        apply sqrt_pos.mpr
        linarith [hinside t ht]
      have hrec : Tendsto (fun t : ℝ => (sqrt (1 - q ^ 2 - t ^ 2))⁻¹)
          (𝓝[<] h) atTop :=
        (tendsto_nhdsWithin_iff.mpr ⟨hdz, hdpos⟩).inv_tendsto_nhdsGT_zero
      have hquot : Tendsto (fun t : ℝ => q * t / sqrt (1 - q ^ 2 - t ^ 2))
          (𝓝[<] h) atTop := by
        have hm := (tendsto_const_nhds.mul hid).pos_mul_atTop (mul_pos hq hh) hrec
        simpa only [div_eq_mul_inv] using hm
      exact (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hquot
    · simp only [hx, if_false]
      have hrpos : 0 < 1 - q ^ 2 - h ^ 2 := by
        rw [hr]
        exact div_pos (sq_pos_of_ne_zero hx) (sq_pos_of_pos hs)
      have hratio : Tendsto (fun t : ℝ => q * t / sqrt (1 - q ^ 2 - t ^ 2))
          (𝓝[<] h) (𝓝 (q * h / sqrt (1 - q ^ 2 - h ^ 2))) :=
        (hid.const_mul q).div hd (ne_of_gt (sqrt_pos.mpr hrpos))
      exact continuous_arctan.continuousAt.tendsto.comp hratio

  have hkh : h ≤ Ck := hb.trans (min_le_left _ _)
  have hroot : sqrt (1 - h ^ 2) ≠ 0 := by
    apply sqrt_ne_zero'.mpr
    have hkbound : h ^ 2 ≤ 1 - k ^ 2 := by
      nlinarith [sq_sqrt hCk.le, sqrt_nonneg (1 - k ^ 2)]
    nlinarith [sq_pos_of_pos hk0]
  have hbase : ContinuousAt (fun t : ℝ => sqrt (1 - t ^ 2)) h :=
    (continuousAt_const.sub (continuousAt_id.pow 2)).sqrt
  have hfh : ContinuousAt f h :=
    continuous_arccos.continuousAt.comp (continuousAt_const.div hbase hroot)
  have hgh : ContinuousAt g h :=
    continuous_arccos.continuousAt.comp (continuousAt_const.div hbase hroot)
  have hEh : ContinuousAt E h :=
    continuousAt_const.max ((continuousAt_const.mul hfh).min
      ((continuousAt_const.mul hgh).min ((hfh.add hgh).sub continuousAt_const)))
  have hc : ContinuousOn E (uIcc (0 : ℝ) h) := by
    rw [uIcc_of_le hh.le]
    exact (SolidGeom.twoCapSlice_continuous k l alpha hk0 hk1 hl0 hl1).mono
      (Icc_subset_Icc le_rfl hb)
  have hi : IntervalIntegrable E volume (0 : ℝ) h := hc.intervalIntegrable
  have hm : Measurable E := by dsimp [E, f, g]; fun_prop
  have hI : ContinuousAt (fun t : ℝ => ∫ z in (0 : ℝ)..t, E z) h :=
    (intervalIntegral.integral_hasDerivAt_right hi
      hm.stronglyMeasurable.stronglyMeasurableAtFilter hEh).continuousAt
  have hmain : Tendsto (fun t : ℝ => t * (f t + g t - alpha)) (𝓝[<] h)
      (𝓝 (h * (f h + g h - alpha))) :=
    hid.mul (((hfh.tendsto.mono_left nhdsWithin_le_nhds).add
      (hgh.tendsto.mono_left nhdsWithin_le_nhds)).sub tendsto_const_nhds)
  have hAk : Tendsto (fun t : ℝ => k * arcsin (t / Ck)) (𝓝[<] h)
      (𝓝 (k * arcsin (h / Ck))) :=
    (continuous_arcsin.continuousAt.tendsto.comp (hid.div_const Ck)).const_mul k
  have hAl : Tendsto (fun t : ℝ => l * arcsin (t / Cl)) (𝓝[<] h)
      (𝓝 (l * arcsin (h / Cl))) :=
    (continuous_arcsin.continuousAt.tendsto.comp (hid.div_const Cl)).const_mul l
  have hF : Tendsto F (𝓝[<] h)
      (𝓝 (h * (f h + g h - alpha) + Tk + Tl - k * arcsin (h / Ck) - l * arcsin (h / Cl))) :=
    (((hmain.add (hatan k Xk hk0 hrk)).add (hatan l Xl hl0 hrl)).sub hAk).sub hAl
  have hEq : (fun t : ℝ => ∫ z in (0 : ℝ)..t, E z) =ᶠ[𝓝[<] h] F := by
    filter_upwards [Ioo_mem_nhdsLT hh] with t ht
    have htsq : t ^ 2 < D / sin alpha ^ 2 := by rw [← hsq]; exact hinside t ht
    exact SolidGeom.twoCapSlice_inner_integral k l alpha t hk0 hk1 hl0 hl1 ha0 hap hD ht.1.le htsq
  exact tendsto_nhds_unique (hI.tendsto.mono_left nhdsWithin_le_nhds) (hF.congr' hEq.symm)

#print axioms proof_SolidGeom_twoCapSlice_integral_threshold
