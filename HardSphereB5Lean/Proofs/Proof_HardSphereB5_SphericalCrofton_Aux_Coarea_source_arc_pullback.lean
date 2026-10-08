import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_arcA_image
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 700000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_arc_pullback (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1)
    (G : Pt → Pt → ℝ) (hG : Measurable (Function.uncurry G)) :
    (∫ u in arcA D, ∫ v in arcB D,
      G (D+u) (D+v) / (‖D‖ * ‖D-e‖ * rA D * rB D) ∂arcMeasure ∂arcMeasure) =
    ∫ α in Set.Icc (-(halfA D)) (halfA D),
      ∫ β in Set.Icc (-(halfB D)) (halfB D),
        G (D+u D α) (D+v D β) / (‖D‖ * ‖D-e‖) := by
  have hD0 : D ≠ 0 := by intro h; exact hoff 0 (by simpa using h)
  have hDe : D-e ≠ 0 := by intro h; exact hoff 1 (by simpa using sub_eq_zero.mp h)
  have ha : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hD0
  have hb : ‖D-e‖ ≠ 0 := norm_ne_zero_iff.mpr hDe
  have hradA : 0 < rA D := by
    have hn : ‖D‖ ≤ 1 := by simpa [LamC, Metric.mem_closedBall, dist_zero_right] using hL.1
    exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg D])
  have hBg := HardSphereB5.SphericalCrofton.Aux.MovingArc.B_chart_geometry D hL hoff hR
  have hradB : 0 < rB D := hBg.2.1
  have hhalfA0 : 0 ≤ halfA D := Real.arccos_nonneg _
  have hhalfApi : halfA D ≤ Real.pi := Real.arccos_le_pi _
  have hu : Measurable (u D) := by unfold u circlePt; fun_prop
  have hv : Measurable (v D) := by unfold v circlePt; fun_prop
  let μA : Measure Pt := arcMeasure.restrict (arcA D)
  let μB : Measure Pt := arcMeasure.restrict (arcB D)
  let νA : Measure ℝ := volume.restrict (Set.Icc (-(halfA D)) (halfA D))
  let νB : Measure ℝ := volume.restrict (Set.Icc (-(halfB D)) (halfB D))
  have hAmap : μA = ENNReal.ofReal (rA D) • νA.map (u D) := by
    have h := SphereGeom.arcMeasure_restrict_circle (cA D) (EA D)
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.EA_orthonormal D hoff) (rA D) hradA
      (-(halfA D)) (halfA D) (by linarith) (by linarith)
    change arcMeasure.restrict (u D '' Set.Icc (-(halfA D)) (halfA D)) =
      ENNReal.ofReal (rA D) • νA.map (u D) at h
    rw [← HardSphereB5.SphericalCrofton.Aux.MovingArc.arcA_image D hL hoff hR] at h
    exact h
  have hBmap : μB = ENNReal.ofReal (rB D) • νB.map (v D) := by
    have h := SphereGeom.arcMeasure_restrict_circle (cB D) (EB D) hBg.1 (rB D) hradB
      (-(halfB D)) (halfB D) (by linarith [hBg.2.2.1]) (by linarith [hBg.2.2.2.1])
    change arcMeasure.restrict (v D '' Set.Icc (-(halfB D)) (halfB D)) =
      ENNReal.ofReal (rB D) • νB.map (v D) at h
    rw [← hBg.2.2.2.2.1] at h
    exact h
  letI : IsFiniteMeasure νB := by dsimp [νB]; infer_instance
  letI : IsFiniteMeasure μB := by
    rw [hBmap]
    exact (νB.map (v D)).smul_finite ENNReal.ofReal_ne_top
  let H : Pt × Pt → ℝ := fun w => G (D+w.1) (D+w.2) / (‖D‖ * ‖D-e‖ * rA D * rB D)
  have hH : Measurable H := by
    unfold H
    exact (hG.comp ((measurable_const.add measurable_fst).prodMk
      (measurable_const.add measurable_snd))).div_const _
  have hinner : StronglyMeasurable (fun u : Pt => ∫ v, H (u,v) ∂μB) :=
    hH.stronglyMeasurable.integral_prod_right'
  have hpullB (u0 : Pt) : (∫ v, H (u0,v) ∂μB) = rB D * ∫ β, H (u0,v D β) ∂νB := by
    have hmeas : Measurable (fun v : Pt => H (u0,v)) :=
      hH.comp (measurable_const.prodMk measurable_id)
    rw [hBmap, integral_smul_measure, integral_map hv.aemeasurable hmeas.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hradB.le, smul_eq_mul]
  change (∫ u, ∫ v, H (u,v) ∂μB ∂μA) = _
  rw [hAmap, integral_smul_measure, integral_map hu.aemeasurable hinner.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hradA.le, smul_eq_mul]
  simp_rw [hpullB]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with α
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with β
  dsimp only [H]
  field_simp [ha,hb,hradA.ne',hradB.ne']
