import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_coordinate_integral
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_integral_reduction
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence_test_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_arcA_image
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_5D_reduction
    (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 → |G D p p'| ≤ C) :
    (∫ D in LamC, ∫ u in arcA D, ∫ v in arcB D,
      (if 0 < dist (D+u) (D+v) ∧ dist (D+u) (D+v) < 1 then
        G D (D+u) (D+v) /
          (‖D‖ * ‖D-e‖ * HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D * HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D)
        else 0) ∂arcMeasure ∂arcMeasure) =
      ∫ x in sourceIncidence, sourceTest G x := by

  let F : Chart5 → ℝ := sourceIncidence.indicator (sourceTest G)
  have hF : Integrable F := (sourceIncidence_test_integrable G hG C hC hbound).integrable_indicator sourceIncidence_measurable
  have hp (D : Pt) : sourceCenter (pack5 (D 0) (D 1) (D 2) 0 0) = D := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sourceCenter, pack5, e, e1, e2]
  have hpc (D : Pt) (α β : ℝ) : sourceCenter (pack5 (D 0) (D 1) (D 2) α β) = D := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sourceCenter, pack5, e, e1, e2]
  have hpa (D : Pt) (α β : ℝ) : (pack5 (D 0) (D 1) (D 2) α β) 3 = α := by simp [pack5]
  have hpb (D : Pt) (α β : ℝ) : (pack5 (D 0) (D 1) (D 2) α β) 4 = β := by simp [pack5]
  have hends (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1)
      (α β : ℝ) (hα : α ∈ Set.Icc (-(halfA D)) (halfA D))
      (hβ : β ∈ Set.Icc (-(halfB D)) (halfB D)) : D+u D α ∈ FA ∧ D+v D β ∈ FB := by
    have ha : u D α ∈ arcA D := by rw [arcA_image D hD hoff hR]; exact ⟨α,hα,rfl⟩
    have hb : v D β ∈ arcB D := by rw [(B_chart_geometry D hD hoff hR).2.2.2.2.1]; exact ⟨β,hβ,rfl⟩
    have hD0 : D ≠ 0 := fun hz => hoff 0 (by simpa using hz)
    have hDe : D ≠ e := fun hz => hoff 1 (by simpa using hz)
    have ha' : u D α ∈ SigmaD D ∧ ‖D + u D α‖ = 1 := by simpa [arcA, hD0] using ha
    have hb' : v D β ∈ SigmaD D ∧ dist (D + v D β) e = 1 := by simpa [arcB, hDe] using hb
    exact ⟨⟨by simpa [Metric.mem_sphere, dist_zero_right] using ha'.2, ha'.1.2.2⟩,
      ⟨hb'.2, hb'.1.2.1⟩⟩
  let J (D : Pt) (α β : ℝ) : ℝ :=
    if 0 < dist (D+u D α) (D+v D β) ∧ dist (D+u D α) (D+v D β) < 1
      then G D (D+u D α) (D+v D β) / (‖D‖ * ‖D-e‖) else 0
  have hpoint (D : Pt) (α β : ℝ) : F (pack5 (D 0) (D 1) (D 2) α β) =
      LamC.indicator (fun D => if offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1 then
        (Set.Icc (-(halfA D)) (halfA D)).indicator (fun α =>
          (Set.Icc (-(halfB D)) (halfB D)).indicator (J D α) β) α else 0) D := by
    have hleft : F (pack5 (D 0) (D 1) (D 2) α β) =
        if offAxis D ∧ D ∈ LamC ∧ Rc ‖D‖ ‖D-e‖ < 1 ∧
          α ∈ Set.Icc (-(halfA D)) (halfA D) ∧ β ∈ Set.Icc (-(halfB D)) (halfB D) ∧
          D+u D α ∈ FA ∧ D+v D β ∈ FB ∧
          0 < dist (D+u D α) (D+v D β) ∧ dist (D+u D α) (D+v D β) < 1
        then G D (D+u D α) (D+v D β) / (‖D‖ * ‖D-e‖) else 0 := by
      simp only [F, Set.indicator, sourceIncidence, Set.mem_setOf_eq, sourceTest,
        sourceEndpointA, sourceEndpointB, hpc, hpa, hpb]
    rw [hleft]
    by_cases hD : D ∈ LamC
    · by_cases hact : offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1
      · by_cases hα : α ∈ Set.Icc (-(halfA D)) (halfA D)
        · by_cases hβ : β ∈ Set.Icc (-(halfB D)) (halfB D)
          · have he := hends D hD hact.1 hact.2 α β hα hβ
            simp only [hD, hact.1, hact.2, hα, hβ, he.1, he.2, true_and,
              Set.indicator_of_mem hD, Set.indicator_of_mem hα, Set.indicator_of_mem hβ,
              if_pos hact, if_true, J]
          · simp [hD, hβ, Set.indicator_of_mem hD, if_pos hact, Set.indicator_of_mem hα]
        · simp [hD, hα, Set.indicator_of_mem hD, if_pos hact]
      · have hn : ¬ (offAxis D ∧ D ∈ LamC ∧ Rc ‖D‖ ‖D-e‖ < 1 ∧
          α ∈ Set.Icc (-(halfA D)) (halfA D) ∧ β ∈ Set.Icc (-(halfB D)) (halfB D) ∧
          D+u D α ∈ FA ∧ D+v D β ∈ FB ∧
          0 < dist (D+u D α) (D+v D β) ∧ dist (D+u D α) (D+v D β) < 1) :=
          fun h => hact ⟨h.1, h.2.2.1⟩
        simp only [if_neg hn, Set.indicator_of_mem hD, if_neg hact]
    · simp [hD, Set.indicator_of_notMem hD]
  have hcoord := source_coordinate_integral F hF
  have hout : (∫ x in sourceIncidence, sourceTest G x) =
      ∫ D in LamC, if offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1 then
        ∫ α in Set.Icc (-(halfA D)) (halfA D),
          ∫ β in Set.Icc (-(halfB D)) (halfB D), J D α β else 0 := by
    rw [← integral_indicator sourceIncidence_measurable]
    change (∫ x, F x) = _
    rw [hcoord]
    simp_rw [hpoint]
    have hLm : MeasurableSet LamC := measurableSet_closedBall.inter measurableSet_closedBall
    rw [← integral_indicator hLm]
    apply integral_congr_ae
    filter_upwards [] with D
    by_cases hD : D ∈ LamC
    · simp only [Set.indicator_of_mem hD]
      by_cases hact : offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1
      · simp only [if_pos hact]
        rw [← integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [] with α
        by_cases hα : α ∈ Set.Icc (-(halfA D)) (halfA D)
        · simp only [Set.indicator_of_mem hα]
          exact integral_indicator measurableSet_Icc
        · simp [Set.indicator_of_notMem hα]
      · simp [hact]
    · simp [Set.indicator_of_notMem hD]
  rw [hout]
  exact source_integral_reduction G hG
