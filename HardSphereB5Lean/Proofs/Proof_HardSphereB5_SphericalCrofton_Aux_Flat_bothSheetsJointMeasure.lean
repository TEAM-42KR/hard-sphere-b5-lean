import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsCroftonMeasure
set_option autoImplicit false
open MeasureTheory HardSphereB5.SphericalCrofton
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 700000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_bothSheetsJointMeasure :
    let μXY := ((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
      ((volume : Measure ℝ).restrict (Set.Ioo 0 1))
    let ν := ((μXY.prod (volume : Measure ℝ)).restrict
      {p : (ℝ × ℝ) × ℝ | 0 < Hpoly p.1.1 p.1.2 p.2}).withDensity
      (fun p => ENNReal.ofReal (1 / Real.sqrt (Hpoly p.1.1 p.1.2 p.2)))
    ν.map (fun p => (p.1, chiPlus p.1.1 p.1.2 p.2)) +
      ν.map (fun p => (p.1, -chiPlus p.1.1 p.1.2 p.2)) =
      μXY.prod ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)) := by
  let μXY := ((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
    ((volume : Measure ℝ).restrict (Set.Ioo 0 1))
  let E : Set ((ℝ × ℝ) × ℝ) := {p | 0 < Hpoly p.1.1 p.1.2 p.2}
  let ρ : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (1 / Real.sqrt (Hpoly p.1.1 p.1.2 p.2))
  let ν : Measure ((ℝ × ℝ) × ℝ) := ((μXY.prod volume).restrict E).withDensity ρ
  let fp : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p => (p.1, chiPlus p.1.1 p.1.2 p.2)
  let fm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p => (p.1, -chiPlus p.1.1 p.1.2 p.2)
  have hE : MeasurableSet E := by unfold E Hpoly; measurability
  have hρ : Measurable ρ := by unfold ρ Hpoly; fun_prop
  have hfp : Measurable fp := by unfold fp chiPlus a0 b0; fun_prop
  have hfm : Measurable fm := by unfold fm chiPlus a0 b0; fun_prop
  have hae : ∀ᵐ xy ∂μXY, 0 < xy.1 ∧ xy.1 < 1 ∧ 0 < xy.2 ∧ xy.2 < 1 := by
    unfold μXY
    rw [Measure.prod_restrict]
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)] with xy hxy
    exact ⟨hxy.1.1, hxy.1.2, hxy.2.1, hxy.2.2⟩
  change ν.map fp + ν.map fm = _
  apply Measure.ext_of_lintegral
  intro g hg
  have hgp : Measurable (fun p => ρ p * g (fp p)) := hρ.mul (hg.comp hfp)
  have hgm : Measurable (fun p => ρ p * g (fm p)) := hρ.mul (hg.comp hfm)
  rw [lintegral_add_measure, lintegral_map hg hfp, lintegral_map hg hfm]
  change (∫⁻ p, g (fp p) ∂((μXY.prod volume).restrict E).withDensity ρ) +
      (∫⁻ p, g (fm p) ∂((μXY.prod volume).restrict E).withDensity ρ) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ
      (show Measurable (fun p => g (fp p)) from hg.comp hfp),
    lintegral_withDensity_eq_lintegral_mul _ hρ
      (show Measurable (fun p => g (fm p)) from hg.comp hfm)]
  rw [← lintegral_indicator hE, ← lintegral_indicator hE]
  simp only [Pi.mul_def]
  rw [lintegral_prod _ (hgp.indicator hE).aemeasurable,
    lintegral_prod _ (hgm.indicator hE).aemeasurable,
    lintegral_prod _ hg.aemeasurable]
  rw [← lintegral_add_left' (Measurable.lintegral_prod_right' (hgp.indicator hE)).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hae] with xy hxy
  let μs := ((volume : Measure ℝ).restrict {s : ℝ | 0 < Hpoly xy.1 xy.2 s}).withDensity
    (fun s => ENNReal.ofReal (1 / Real.sqrt (Hpoly xy.1 xy.2 s)))
  have hmaps : μs.map (chiPlus xy.1 xy.2) + μs.map (fun s => -chiPlus xy.1 xy.2 s) =
      volume.restrict (Set.Ioo (-Real.pi) Real.pi) :=
    HardSphereB5.SphericalCrofton.Aux.Flat.bothSheetsCroftonMeasure xy.1 xy.2 hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2
  have hgg : Measurable (fun χ : ℝ => g (xy, χ)) := hg.comp (measurable_const.prodMk measurable_id)
  have hc : Measurable (chiPlus xy.1 xy.2) := by unfold chiPlus; fun_prop
  have hn : Measurable (fun s => -chiPlus xy.1 xy.2 s) := hc.neg
  have hw : Measurable (fun s => ENNReal.ofReal (1 / Real.sqrt (Hpoly xy.1 xy.2 s))) := by
    unfold Hpoly; fun_prop
  have hh := congrArg (fun m : Measure ℝ => ∫⁻ χ, g (xy,χ) ∂m) hmaps
  rw [lintegral_add_measure, lintegral_map hgg hc, lintegral_map hgg hn] at hh
  dsimp only [μs] at hh
  rw [lintegral_withDensity_eq_lintegral_mul _ hw
      (show Measurable (fun s => g (xy, chiPlus xy.1 xy.2 s)) from hgg.comp hc),
    lintegral_withDensity_eq_lintegral_mul _ hw
      (show Measurable (fun s => g (xy, -chiPlus xy.1 xy.2 s)) from hgg.comp hn)] at hh
  rw [← lintegral_indicator (by unfold Hpoly; measurability),
    ← lintegral_indicator (by unfold Hpoly; measurability)] at hh
  simpa only [Set.indicator, Set.mem_setOf_eq, Pi.mul_apply, E, ρ, fp, fm] using hh
