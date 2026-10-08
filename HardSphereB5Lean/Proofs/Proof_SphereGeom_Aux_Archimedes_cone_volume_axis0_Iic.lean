import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

private theorem acceptedSliceIntegral (k : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1) :
    (∫ z in Set.Icc (0 : ℝ) 1,
      Real.pi * min ((1 - k ^ 2) * z ^ 2 / k ^ 2) (1 - z ^ 2)) =
      (2 * Real.pi / 3) * (1 - k) := by
  have hkne : k ≠ 0 := ne_of_gt hk0
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk0
  let f : ℝ → ℝ := fun z =>
    Real.pi * min ((1 - k ^ 2) * z ^ 2 / k ^ 2) (1 - z ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hleft : (∫ z in (0 : ℝ)..k, f z) =
      Real.pi * ((1 - k ^ 2) / k ^ 2) * (k ^ 3 / 3) := by
    calc
      (∫ z in (0 : ℝ)..k, f z) =
          ∫ z in (0 : ℝ)..k, (Real.pi * ((1 - k ^ 2) / k ^ 2)) * z ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [Set.uIcc_of_le hk0.le] at hz
        have hsq : z ^ 2 ≤ k ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hz.2)
            (show 0 ≤ k + z by linarith [hz.1])]
        have hm : (1 - k ^ 2) * z ^ 2 / k ^ 2 ≤ 1 - z ^ 2 := by
          apply (div_le_iff₀ hk2).mpr
          nlinarith [hsq]
        dsimp [f]
        rw [min_eq_left hm]
        ring
      _ = Real.pi * ((1 - k ^ 2) / k ^ 2) * (k ^ 3 / 3) := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        norm_num
  have hright : (∫ z in k..(1 : ℝ), f z) =
      Real.pi * ((1 - k) - (1 - k ^ 3) / 3) := by
    calc
      (∫ z in k..(1 : ℝ), f z) =
          ∫ z in k..(1 : ℝ), Real.pi * (1 - z ^ 2) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [Set.uIcc_of_le hk1] at hz
        have hsq : k ^ 2 ≤ z ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hz.1)
            (show 0 ≤ z + k by linarith [hz.1])]
        have hm : 1 - z ^ 2 ≤ (1 - k ^ 2) * z ^ 2 / k ^ 2 := by
          apply (le_div_iff₀ hk2).mpr
          nlinarith [hsq]
        dsimp [f]
        rw [min_eq_right hm]
      _ = Real.pi * ((1 - k) - (1 - k ^ 3) / 3) := by
        have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume k 1 :=
          intervalIntegrable_const
        have hp : IntervalIntegrable (fun z : ℝ => z ^ 2) volume k 1 :=
          (continuous_id.pow 2).intervalIntegrable k 1
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hc hp,
          intervalIntegral.integral_const, integral_pow]
        norm_num
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  change (∫ z in (0 : ℝ)..1, f z) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 k) (hf.intervalIntegrable k 1), hleft, hright]
  field_simp
  <;> ring

private noncomputable def axialMerge : (ℝ × EuclideanSpace ℝ (Fin 2)) ≃ᵐ E3 :=
  ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.trans
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))

private lemma axialMerge_mp : MeasurePreserving axialMerge := by
  have h1 : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) := by
    exact (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin 2))
  exact (PiLp.volume_preserving_toLp (Fin 3)).comp
    (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm).comp h1)

private lemma axialMerge_coord (z : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : axialMerge (z, y) 0 = z := by
  simp [axialMerge, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

private lemma axialMerge_norm_sq (z : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    ‖axialMerge (z, y)‖ ^ 2 = z ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [axialMerge, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.sum_univ_succ, Fin.insertNth_zero]

private lemma axis_upper_measurable (k : ℝ) :
    MeasurableSet {x : E3 | ‖x‖ ≤ 1 ∧ k * ‖x‖ ≤ x 0} := by
  exact (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_le (measurable_const.mul measurable_norm)
      ((measurable_pi_apply 0).comp (PiLp.volume_preserving_ofLp (Fin 3)).measurable))

private lemma axis_upper_slice (k : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    (fun y : EuclideanSpace ℝ (Fin 2) => axialMerge (z, y)) ⁻¹'
      {x : E3 | ‖x‖ ≤ 1 ∧ k * ‖x‖ ≤ x 0} =
    Metric.closedBall 0 (Real.sqrt (min ((1 - k ^ 2) * z ^ 2 / k ^ 2) (1 - z ^ 2))) := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk0
  have hk2le : k ^ 2 ≤ 1 := by nlinarith
  have ha : 0 ≤ (1 - k ^ 2) * z ^ 2 / k ^ 2 := by positivity
  have hb : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hm : 0 ≤ min ((1 - k ^ 2) * z ^ 2 / k ^ 2) (1 - z ^ 2) := le_min ha hb
  ext y
  have hn := axialMerge_norm_sq z y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, axialMerge_coord, Metric.mem_closedBall,
    dist_zero_right, Real.le_sqrt (norm_nonneg y) hm, le_min_iff]
  constructor
  · rintro ⟨hn1, hkc⟩
    have hkr : 0 ≤ k * ‖axialMerge (z, y)‖ := mul_nonneg hk0.le (norm_nonneg _)
    have hsq : (k * ‖axialMerge (z, y)‖) ^ 2 ≤ z ^ 2 :=
      (sq_le_sq₀ hkr hz.1).2 hkc
    refine ⟨(le_div_iff₀ hk2).2 ?_, ?_⟩
    · nlinarith
    · nlinarith [norm_nonneg (axialMerge (z, y))]
  · rintro ⟨ha1, hb1⟩
    have hasq := (le_div_iff₀ hk2).1 ha1
    refine ⟨?_, ?_⟩
    · nlinarith [norm_nonneg (axialMerge (z, y))]
    · have hsq : (k * ‖axialMerge (z, y)‖) ^ 2 ≤ z ^ 2 := by nlinarith
      exact (sq_le_sq₀ (mul_nonneg hk0.le (norm_nonneg _)) hz.1).1 hsq

private lemma axis_upper_slice_empty (k : ℝ) (hk0 : 0 < k)
    (z : ℝ) (hz : z ∉ Set.Icc (0 : ℝ) 1) :
    (fun y : EuclideanSpace ℝ (Fin 2) => axialMerge (z, y)) ⁻¹'
      {x : E3 | ‖x‖ ≤ 1 ∧ k * ‖x‖ ≤ x 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro y hy
  have hn := axialMerge_norm_sq z y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, axialMerge_coord] at hy
  have hz0 : 0 ≤ z := (mul_nonneg hk0.le (norm_nonneg _)).trans hy.2
  have hz1 : z ≤ 1 := by nlinarith [sq_nonneg ‖y‖, norm_nonneg (axialMerge (z, y))]
  exact hz ⟨hz0, hz1⟩

private theorem upperConeProof (k : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1) :
  (volume : Measure E3) {x : E3 | ‖x‖ ≤ 1 ∧ k * ‖x‖ ≤ x 0} =
  ENNReal.ofReal ((2 * Real.pi / 3) * (1 - k)) := by
  let C : Set E3 := {x : E3 | ‖x‖ ≤ 1 ∧ k * ‖x‖ ≤ x 0}
  let f : ℝ → ℝ := fun z => Real.pi * min ((1-k^2)*z^2/k^2) (1-z^2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfi : IntegrableOn f (Set.Icc (0 : ℝ) 1) := hf.integrableOn_Icc
  have hnn (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ f z := by
    have hk2 : k^2 ≤ 1 := by nlinarith
    have ha : 0 ≤ (1-k^2)*z^2/k^2 := by positivity
    have hb : 0 ≤ 1-z^2 := by nlinarith [hz.1, hz.2]
    exact mul_nonneg Real.pi_pos.le (le_min ha hb)
  have hsec (z : ℝ) :
      (volume : Measure (EuclideanSpace ℝ (Fin 2)))
        ((Prod.mk z) ⁻¹' (axialMerge ⁻¹' C)) =
      (Set.Icc (0 : ℝ) 1).indicator (fun z => ENNReal.ofReal (f z)) z := by
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hz]
      change (volume : Measure (EuclideanSpace ℝ (Fin 2)))
        ((fun y => axialMerge (z,y)) ⁻¹' C) = ENNReal.ofReal (f z)
      rw [axis_upper_slice k hk0 hk1 z hz, EuclideanSpace.volume_closedBall_fin_two]
      have hk2 : k^2 ≤ 1 := by nlinarith
      have ha : 0 ≤ (1-k^2)*z^2/k^2 := by positivity
      have hb : 0 ≤ 1-z^2 := by nlinarith [hz.1,hz.2]
      have hm : 0 ≤ min ((1-k^2)*z^2/k^2) (1-z^2) := le_min ha hb
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt hm,
        ← ENNReal.ofReal_mul hm]
      congr 1
      exact mul_comm _ _
    · rw [Set.indicator_of_notMem hz]
      change (volume : Measure (EuclideanSpace ℝ (Fin 2)))
        ((fun y => axialMerge (z,y)) ⁻¹' C) = 0
      rw [axis_upper_slice_empty k hk0 z hz, measure_empty]
  calc
    (volume : Measure E3) C = (volume : Measure (ℝ × EuclideanSpace ℝ (Fin 2)))
        (axialMerge ⁻¹' C) :=
      (axialMerge_mp.measure_preimage (axis_upper_measurable k).nullMeasurableSet).symm
    _ = ∫⁻ z : ℝ, (volume : Measure (EuclideanSpace ℝ (Fin 2)))
        ((Prod.mk z) ⁻¹' (axialMerge ⁻¹' C)) :=
      Measure.prod_apply ((axis_upper_measurable k).preimage axialMerge.measurable)
    _ = ∫⁻ z : ℝ, (Set.Icc (0 : ℝ) 1).indicator (fun z => ENNReal.ofReal (f z)) z :=
      lintegral_congr hsec
    _ = ∫⁻ z : ℝ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (f z) :=
      lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (∫ z in Set.Icc (0 : ℝ) 1, f z) :=
      (ofReal_integral_eq_lintegral_ofReal hfi
        ((ae_restrict_mem measurableSet_Icc).mono hnn)).symm
    _ = ENNReal.ofReal ((2 * Real.pi / 3) * (1-k)) := by
      rw [acceptedSliceIntegral k hk0 hk1]

private lemma axis_boundary_measurable (k : ℝ) :
    MeasurableSet {x : E3 | x 0 = k * ‖x‖} := by
  exact measurableSet_eq_fun
    ((measurable_pi_apply 0).comp (PiLp.volume_preserving_ofLp (Fin 3)).measurable)
    (measurable_const.mul measurable_norm)

private theorem axisBoundaryProof (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
  (volume : Measure E3) {x : E3 | x 0 = k * ‖x‖} = 0 := by
  let C : Set E3 := {x : E3 | x 0 = k * ‖x‖}
  have hmeas : MeasurableSet C := axis_boundary_measurable k
  rw [← axialMerge_mp.measure_preimage hmeas.nullMeasurableSet]
  change ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (axialMerge ⁻¹' C) = 0
  rw [Measure.prod_apply (hmeas.preimage axialMerge.measurable)]
  by_cases hk : k = 0
  · subst k
    have hnot : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
      rw [ae_iff]
      simp
    calc
      (∫⁻ z : ℝ, (volume : Measure (EuclideanSpace ℝ (Fin 2)))
        ((Prod.mk z) ⁻¹' (axialMerge ⁻¹' C))) = ∫⁻ _ : ℝ, (0 : ENNReal) := by
          apply lintegral_congr_ae
          filter_upwards [hnot] with z hz
          have hempty : (Prod.mk z) ⁻¹' (axialMerge ⁻¹' C) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.2
            intro y hy
            simp only [Set.mem_preimage, C, Set.mem_setOf_eq, axialMerge_coord, zero_mul] at hy
            exact hz hy
          rw [hempty, measure_empty]
      _ = 0 := by simp
  · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk)
    have hk2 : 0 < k^2 := sq_pos_of_pos hkpos
    have hk2le : k^2 ≤ 1 := by nlinarith
    have hsec (z : ℝ) :
        (volume : Measure (EuclideanSpace ℝ (Fin 2)))
          ((Prod.mk z) ⁻¹' (axialMerge ⁻¹' C)) = 0 := by
      have ha : 0 ≤ (1-k^2)*z^2/k^2 := by positivity
      apply measure_mono_null (t := Metric.sphere 0 (Real.sqrt ((1-k^2)*z^2/k^2)))
      · intro y hy
        simp only [Set.mem_preimage, C, Set.mem_setOf_eq, axialMerge_coord] at hy
        have hn := axialMerge_norm_sq z y
        have hsq : ‖y‖^2 = (1-k^2)*z^2/k^2 := by
          apply (eq_div_iff hk2.ne').2
          nlinarith [congrArg (fun t : ℝ => t^2) hy]
        simp only [Metric.mem_sphere, dist_zero_right]
        exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
          (hsq.trans (Real.sq_sqrt ha).symm)
      · exact Measure.addHaar_sphere volume _ _
    simp_rw [hsec]
    simp

private theorem lowerConeProof (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
  (volume : Measure E3) {x : E3 | ‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖} =
  ENNReal.ofReal ((2 * Real.pi / 3) * (h + 1)) := by
  let B : Set E3 := {x | ‖x‖ ≤ 1}
  let L : Set E3 := {x | ‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖}
  let U : Set E3 := {x | ‖x‖ ≤ 1 ∧ h * ‖x‖ ≤ x 0}
  have hLmeas : MeasurableSet L :=
    (measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le
        ((measurable_pi_apply 0).comp (PiLp.volume_preserving_ofLp (Fin 3)).measurable)
        (measurable_const.mul measurable_norm))
  have hUmeas : MeasurableSet U := axis_upper_measurable h
  have hB : (volume : Measure E3) B = ENNReal.ofReal (Real.pi * 4 / 3) := by
    have hset : B = Metric.closedBall (0 : E3) 1 := by
      ext x
      simp [B, Metric.mem_closedBall]
    rw [hset, EuclideanSpace.volume_closedBall_fin_three]
    simp
  have hunion : L ∪ U = B := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro hx
      rcases le_total (x 0) (h * ‖x‖) with hle | hle
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr ⟨hx, hle⟩
  have hinter : (volume : Measure E3) (L ∩ U) = 0 := by
    apply measure_mono_null (t := {x : E3 | x 0 = h * ‖x‖})
    · intro x hx
      exact le_antisymm hx.1.2 hx.2.2
    · exact axisBoundaryProof h hh0 hh1
  have hsum : (volume : Measure E3) L + (volume : Measure E3) U =
      ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [← measure_union_add_inter L hUmeas, hunion, hinter, add_zero, hB]
  by_cases heq : h = 0
  · subst h
    have hneg : (LinearIsometryEquiv.neg ℝ (E := E3)) ⁻¹' L = U := by
      ext x
      change (‖-x‖ ≤ 1 ∧ (-x) 0 ≤ (0 : ℝ) * ‖-x‖) ↔
        (‖x‖ ≤ 1 ∧ (0 : ℝ) * ‖x‖ ≤ x 0)
      simp only [norm_neg, PiLp.neg_apply, zero_mul]
      constructor <;> rintro ⟨hn, hx⟩ <;> exact ⟨hn, by linarith⟩
    have hsym : (volume : Measure E3) U = (volume : Measure E3) L := by
      rw [← hneg]
      exact (LinearIsometryEquiv.neg ℝ (E := E3)).measurePreserving.measure_preimage
        hLmeas.nullMeasurableSet
    rw [hsym] at hsum
    have hLfin : (volume : Measure E3) L ≠ ⊤ :=
      measure_ne_top_of_subset (s := B) (t := L) (fun _ hx => hx.1)
        (by rw [hB]; exact ENNReal.ofReal_ne_top)
    have ht := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add hLfin hLfin,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)] at ht
    calc
      (volume : Measure E3) L = ENNReal.ofReal ((volume : Measure E3) L).toReal :=
        (ENNReal.ofReal_toReal hLfin).symm
      _ = ENNReal.ofReal ((2 * Real.pi / 3) * ((0 : ℝ) + 1)) := by
        congr 1
        linarith
  · have hp : 0 < h := lt_of_le_of_ne hh0 (Ne.symm heq)
    have hUvol : (volume : Measure E3) U =
        ENNReal.ofReal ((2 * Real.pi / 3) * (1-h)) := upperConeProof h hp hh1
    have hUfin : (volume : Measure E3) U ≠ ⊤ := by
      rw [hUvol]
      exact ENNReal.ofReal_ne_top
    calc
      (volume : Measure E3) L =
          ((volume : Measure E3) L + (volume : Measure E3) U) - (volume : Measure E3) U :=
        (ENNReal.add_sub_cancel_right hUfin).symm
      _ = ENNReal.ofReal (Real.pi * 4 / 3) - ENNReal.ofReal ((2 * Real.pi / 3) * (1-h)) := by
        rw [hsum, hUvol]
      _ = ENNReal.ofReal (Real.pi * 4 / 3 - (2 * Real.pi / 3) * (1-h)) :=
        (ENNReal.ofReal_sub _ (mul_nonneg (by positivity) (sub_nonneg.2 hh1))).symm
      _ = ENNReal.ofReal ((2 * Real.pi / 3) * (h+1)) := by
        congr 1
        ring

private theorem radialConeProof (h : ℝ) :
  Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
    {u : Metric.sphere (0 : E3) 1 | inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (u : E3) ≤ h}) =
  {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    have hn : ‖(u : E3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    have hc : (u : E3) 0 ≤ h := by
      simpa only [Set.mem_setOf_eq, EuclideanSpace.inner_single_left, map_one, one_mul] using hu
    have hm := mul_le_mul_of_nonneg_left hc hr.1.le
    refine ⟨?_, ?_, ?_⟩
    · simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hn, mul_one] using hr.1
    · simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hn, mul_one] using hr.2
    · simpa only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr.1, hn, mul_one, mul_comm] using hm
  · rintro ⟨hx0, hx1, hxc⟩
    let u : E3 := ‖x‖⁻¹ • x
    have hn : ‖u‖ = 1 := by
      simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx0,
        inv_mul_cancel₀ hx0.ne']
    have hc : inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) u ≤ h := by
      simp only [EuclideanSpace.inner_single_left, map_one, one_mul, u,
        PiLp.smul_apply, smul_eq_mul, ← div_eq_inv_mul]
      exact (div_le_iff₀ hx0).2 hxc
    refine ⟨‖x‖, ⟨hx0, hx1⟩, u, ?_, ?_⟩
    · exact ⟨⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩, hc, rfl⟩
    · simp only [u, smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]

private theorem negativeConeProof (h : ℝ) (hm : -1 < h) (hn : h < 0) :
    (volume : Measure E3) (Set.Ioo (0 : ℝ) 1 •
      ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
        {u : Metric.sphere (0 : E3) 1 | inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (u : E3) ≤ h})) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (min h 1 + 1)) := by
  rw [radialConeProof]
  let U : Set E3 := {x : E3 | ‖x‖ ≤ 1 ∧ (-h) * ‖x‖ ≤ x 0}
  let C : Set E3 := {x : E3 | ‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖}
  have hcneg : C = (fun x : E3 => -x) ⁻¹' U := by
    ext x
    change (‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖) ↔
      (‖-x‖ ≤ 1 ∧ (-h) * ‖-x‖ ≤ (-x) 0)
    rw [norm_neg]
    change (‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖) ↔
      (‖x‖ ≤ 1 ∧ (-h) * ‖x‖ ≤ -x 0)
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, by nlinarith⟩
    · rintro ⟨ha, hb⟩
      exact ⟨ha, by nlinarith⟩
  have hzero : ∀ᵐ x : E3 ∂volume, x ∉ ({0} : Set E3) :=
    compl_mem_ae_iff.mpr (measure_singleton (0 : E3))
  have hsphere : ∀ᵐ x : E3 ∂volume, x ∉ Metric.sphere (0 : E3) 1 :=
    compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0 : E3) 1)
  have heq : {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} =ᵐ[volume] C := by
    filter_upwards [hzero, hsphere] with x hz hs
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa only [Set.mem_singleton_iff] using hz)
    have hnorm_ne : ‖x‖ ≠ 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hs
    apply propext
    change (0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖) ↔
      (‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖)
    constructor
    · intro hx
      exact ⟨hx.2.1.le, hx.2.2⟩
    · intro hx
      have hlt : ‖x‖ < 1 := by
        rcases lt_or_eq_of_le hx.1 with hlt | heq
        · exact hlt
        · exact (hnorm_ne heq).elim
      exact ⟨hpos, hlt, hx.2⟩
  calc
    (volume : Measure E3) {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} =
        (volume : Measure E3) C := measure_congr heq
    _ = (volume : Measure E3) U := by
      rw [hcneg]
      exact Measure.measure_preimage_neg volume U
    _ = ENNReal.ofReal ((2 * Real.pi / 3) * (1 - (-h))) :=
      upperConeProof (-h) (neg_pos.mpr hn) (by linarith)
    _ = ENNReal.ofReal ((2 * Real.pi / 3) * (min h 1 + 1)) := by
      rw [min_eq_left (show h ≤ 1 by linarith)]
      congr 1
      ring

private theorem extremeConeProof (h : ℝ) (hext : h ≤ -1 ∨ 1 ≤ h) :
    (volume : Measure E3) (Set.Ioo (0 : ℝ) 1 •
      ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
        {u : Metric.sphere (0 : E3) 1 | inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (u : E3) ≤ h})) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (min h 1 + 1)) := by
  rw [radialConeProof]
  rcases hext with hh | hh
  · let S : Submodule ℝ E3 :=
      { carrier := {x | x (1 : Fin 3) = 0}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          change x 1 + y 1 = 0
          rw [hx, hy]
          norm_num
        smul_mem' := by
          intro c x hx
          change c * x 1 = 0
          rw [hx]
          ring }
    have hS : S ≠ ⊤ := by
      intro heq
      have hv : EuclideanSpace.single (1 : Fin 3) (1 : ℝ) ∈ S := by
        rw [heq]
        trivial
      change (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E3) 1 = 0 at hv
      simpa using hv
    have hsub : {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} ⊆ (S : Set E3) := by
      intro x hx
      have hb : |x 0| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (0 : Fin 3)
      have hm : h * ‖x‖ ≤ -‖x‖ := by
        calc
          h * ‖x‖ ≤ (-1) * ‖x‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg x)
          _ = -‖x‖ := by ring
      have hxeq : x 0 = -‖x‖ := le_antisymm (hx.2.2.trans hm) (abs_le.mp hb).1
      have hs' : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
        simpa [Fin.sum_univ_succ, add_assoc] using EuclideanSpace.real_norm_sq_eq x
      rw [hxeq] at hs'
      have hz : (x 1) ^ 2 = 0 := by nlinarith [sq_nonneg (x 2)]
      change x 1 = 0
      exact sq_eq_zero_iff.mp hz
    have hv : (volume : Measure E3) {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} = 0 :=
      measure_mono_null hsub (Measure.addHaar_submodule volume S hS)
    rw [hv]
    have hr : (2 * Real.pi / 3) * (min h 1 + 1) ≤ 0 := by
      rw [min_eq_left (show h ≤ 1 by linarith)]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    exact (ENNReal.ofReal_eq_zero.mpr hr).symm
  · have heq : {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} =
        Metric.ball (0 : E3) 1 \ {0} := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · simpa only [Metric.mem_ball, dist_zero_right] using hx.2.1
        · simpa only [Set.mem_singleton_iff] using (norm_pos_iff.mp hx.1)
      · rintro ⟨hball, hne⟩
        have hn : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa only [Set.mem_singleton_iff] using hne)
        have hb : |x 0| ≤ ‖x‖ := by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (0 : Fin 3)
        refine ⟨hn, ?_, ?_⟩
        · simpa only [Metric.mem_ball, dist_zero_right] using hball
        · have hx : x 0 ≤ ‖x‖ := (le_abs_self (x 0)).trans hb
          nlinarith [mul_nonneg (sub_nonneg.mpr hh) (norm_nonneg x)]
    rw [heq, measure_sdiff_null (measure_singleton (0 : E3)),
      EuclideanSpace.volume_ball_fin_three, min_eq_right hh]
    norm_num
    congr 1
    ring

theorem proof_SphereGeom_Aux_Archimedes_cone_volume_axis0_Iic (h : ℝ) :
    (volume : Measure E3) (Set.Ioo (0 : ℝ) 1 •
      ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
        {u : Metric.sphere (0 : E3) 1 | inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (u : E3) ≤ h})) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (min h 1 + 1)) := by
  by_cases hleft : h ≤ -1
  · exact extremeConeProof h (Or.inl hleft)
  by_cases hright : 1 ≤ h
  · exact extremeConeProof h (Or.inr hright)
  have hm : -1 < h := lt_of_not_ge hleft
  have hh1 : h ≤ 1 := (lt_of_not_ge hright).le
  by_cases hn : h < 0
  · exact negativeConeProof h hm hn
  have hh0 : 0 ≤ h := le_of_not_gt hn
  rw [radialConeProof h]
  let C : Set E3 := {x | ‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖}
  have hzero : ∀ᵐ x : E3 ∂volume, x ∉ ({0} : Set E3) :=
    compl_mem_ae_iff.mpr (measure_singleton (0 : E3))
  have hsphere : ∀ᵐ x : E3 ∂volume, x ∉ Metric.sphere (0 : E3) 1 :=
    compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0 : E3) 1)
  have heq : {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} =ᵐ[volume] C := by
    filter_upwards [hzero, hsphere] with x hz hs
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa only [Set.mem_singleton_iff] using hz)
    have hnorm_ne : ‖x‖ ≠ 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hs
    apply propext
    change (0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖) ↔
      (‖x‖ ≤ 1 ∧ x 0 ≤ h * ‖x‖)
    constructor
    · intro hx
      exact ⟨hx.2.1.le, hx.2.2⟩
    · intro hx
      exact ⟨hpos, lt_of_le_of_ne hx.1 hnorm_ne, hx.2⟩
  calc
    (volume : Measure E3) {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x 0 ≤ h * ‖x‖} =
        (volume : Measure E3) C := measure_congr heq
    _ = ENNReal.ofReal ((2 * Real.pi / 3) * (h+1)) := lowerConeProof h hh0 hh1
    _ = ENNReal.ofReal ((2 * Real.pi / 3) * (min h 1+1)) := by rw [min_eq_left hh1]
