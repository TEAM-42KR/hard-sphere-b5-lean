import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_signed_endpoint_measures
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_pullback
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_contact_distances
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_pair_inverse_distance
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_endpoint_frame_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_coordinates_preserving
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false

open MeasureTheory Set Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical ENNReal
noncomputable section
set_option maxHeartbeats 1800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_5D_reduction
    (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 → |G D p p'| ≤ C) :
    ∫ p in FA, ∫ p' in FB,
        (if 0 < dist p p' ∧ dist p p' < 1 then (dist p p')⁻¹ *
          ∫ q in {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (p'-p) = 0 ∧
            midpoint ℝ p p' + √(1-dist p p'^2/4) • q ∈ LamC},
            G (midpoint ℝ p p' + √(1-dist p p'^2/4) • q) p p' ∂arcMeasure
          else 0) ∂sphereMeasure e ∂sphereMeasure 0 =
      ∫ y in targetIncidence, targetTest G y := by
  haveI (c : Pt) : IsFiniteMeasure (sphereMeasure c) := ⟨by
    rw [sphereMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  let μA : Measure Pt := (sphereMeasure 0).restrict FA
  let μB : Measure Pt := (sphereMeasure e).restrict FB
  let ν : Measure (Pt × Pt) := μA.prod μB
  let μψ : Measure ℝ := volume.restrict (Icc (-π) π)
  have hFA : MeasurableSet FA := Metric.isClosed_sphere.measurableSet.inter measurableSet_closedBall
  have hFB : MeasurableSet FB := Metric.isClosed_sphere.measurableSet.inter measurableSet_closedBall
  have hLam : MeasurableSet LamC := measurableSet_closedBall.inter measurableSet_closedBall
  let D : (Pt × Pt) × ℝ → Pt := fun w => midpoint ℝ w.1.1 w.1.2 +
    Real.sqrt (1-dist w.1.1 w.1.2^2/4) •
      (Real.cos w.2 • centerFrame0 (w.1.2-w.1.1)+Real.sin w.2 • centerFrame1 (w.1.2-w.1.1))
  have hDm : Measurable D := by
    dsimp [D,centerFrame0,centerFrame1,unitDir]
    simp only [midpoint_eq_smul_add]
    unfold cross crossProduct
    fun_prop
  have hsep : Measurable (fun w : (Pt × Pt) × ℝ => dist w.1.1 w.1.2) := by fun_prop
  let M : (Pt × Pt) × ℝ → ℝ := fun w =>
    if (0 < dist w.1.1 w.1.2 ∧ dist w.1.1 w.1.2 < 1) ∧ D w ∈ LamC
    then G (D w) w.1.1 w.1.2 / dist w.1.1 w.1.2 else 0
  have hMm : Measurable M := by
    apply Measurable.ite (((measurableSet_lt measurable_const hsep).inter
      (measurableSet_lt hsep measurable_const)).inter (hLam.preimage hDm)) _ measurable_const
    exact (hG.comp (hDm.prodMk measurable_fst)).div hsep
  have hpair : ∀ᵐ pq : Pt × Pt ∂ν, pq.1 ∈ FA ∧ pq.2 ∈ FB := by
    apply (Measure.ae_prod_iff_ae_ae (hFA.prod hFB)).mpr
    filter_upwards [ae_restrict_mem hFA] with p hp
    filter_upwards [ae_restrict_mem hFB] with q hq
    exact ⟨hp,hq⟩
  have hframe : ∀ᵐ pq : Pt × Pt ∂ν, centerFrame0 (pq.2-pq.1) ≠ 0 :=
    target_endpoint_frame_ae
  have hmajor : Integrable (fun w : (Pt × Pt) × ℝ => C*(dist w.1.1 w.1.2)⁻¹)
      (ν.prod μψ) := by
    have h := (sphere_pair_inverse_distance.const_mul C).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μψ)
    simpa only [mul_one] using h
  have hM : Integrable M (ν.prod μψ) := by
    apply hmajor.mono' hMm.aestronglyMeasurable
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hpair,
      Measure.quasiMeasurePreserving_fst.ae hframe] with w hw hf
    by_cases hs : (0 < dist w.1.1 w.1.2 ∧ dist w.1.1 w.1.2 < 1) ∧ D w ∈ LamC
    · have hc := center_circle_contact_distances w.1.1 w.1.2 hs.1.1 (by linarith [hs.1.2]) hf w.2
      have hb := hbound (D w) hs.2 w.1.1 hw.1 w.1.2 hw.2 hc.1 hc.2 hs.1.1 hs.1.2
      rw [show M w = G (D w) w.1.1 w.1.2 / dist w.1.1 w.1.2 from if_pos hs,
        Real.norm_eq_abs,abs_div,abs_of_pos hs.1.1]
      simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hb hs.1.1.le
    · rw [show M w = 0 from if_neg hs,norm_zero]
      exact mul_nonneg hC (inv_nonneg.mpr dist_nonneg)
  let J : Pt × Pt → ℝ := fun pq =>
    if 0 < dist pq.1 pq.2 ∧ dist pq.1 pq.2 < 1 then (dist pq.1 pq.2)⁻¹ *
      ∫ q in {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (pq.2-pq.1) = 0 ∧
        midpoint ℝ pq.1 pq.2 + Real.sqrt (1-dist pq.1 pq.2^2/4) • q ∈ LamC},
        G (midpoint ℝ pq.1 pq.2 + Real.sqrt (1-dist pq.1 pq.2^2/4) • q) pq.1 pq.2 ∂arcMeasure
    else 0
  have hJae : J =ᵐ[ν] (fun pq => ∫ ψ, M (pq,ψ) ∂μψ) := by
    filter_upwards [hframe] with pq hf
    by_cases hs : 0 < dist pq.1 pq.2 ∧ dist pq.1 pq.2 < 1
    · have hg : Measurable (fun c : Pt => G c pq.1 pq.2) :=
        hG.comp (measurable_id.prodMk measurable_const)
      have hpull := center_circle_pullback pq.1 pq.2
        (sub_ne_zero.mpr (dist_pos.mp hs.1).symm) hf _ hg
      dsimp only [J]
      rw [if_pos hs,hpull,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ψ
      change (dist pq.1 pq.2)⁻¹ *
        (if D (pq,ψ) ∈ LamC then G (D (pq,ψ)) pq.1 pq.2 else 0) = M (pq,ψ)
      by_cases hc : D (pq,ψ) ∈ LamC
      · rw [if_pos hc,show M (pq,ψ) = G (D (pq,ψ)) pq.1 pq.2 / dist pq.1 pq.2 from if_pos ⟨hs,hc⟩]
        ring
      · rw [if_neg hc,show M (pq,ψ) = 0 from if_neg (by rintro ⟨_,h⟩; exact hc h)]
        ring
    · simp only [J,if_neg hs]
      have hz : (fun ψ : ℝ => M (pq,ψ)) = 0 := by
        funext ψ
        exact if_neg (by rintro ⟨h,_⟩; exact hs h)
      rw [hz]
      change (0 : ℝ) = ∫ ψ : ℝ, (0 : ℝ) ∂μψ
      simp only [integral_zero]
  have hJi : Integrable J ν := hM.integral_prod_left.congr hJae.symm
  let SA : Set (ℝ × ℝ) := Icc (1/2 : ℝ) 1 ×ˢ Icc (-π) π
  let SB : Set (ℝ × ℝ) := Icc (-1 : ℝ) (-1/2) ×ˢ Icc (-π) π
  let μa : Measure (ℝ × ℝ) := volume.restrict SA
  let μb : Measure (ℝ × ℝ) := volume.restrict SB
  let A : ℝ × ℝ → Pt := fun a => endpointCylinder a.1 a.2
  let B : ℝ × ℝ → Pt := fun b => e+endpointCylinder b.1 b.2
  let F : (ℝ × ℝ) × (ℝ × ℝ) → Pt × Pt := Prod.map A B
  let T : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) → (Pt × Pt) × ℝ := Prod.map F id
  have hA : Measurable A := by dsimp [A,endpointCylinder]; fun_prop
  have hB : Measurable B := by dsimp [B,endpointCylinder]; fun_prop
  have hF : Measurable F := hA.prodMap hB
  have hT : Measurable T := hF.prodMap measurable_id
  have hEP : ν = (μa.prod μb).map F := by
    dsimp [ν,μA,μB]
    rw [signed_endpoint_measures.1,signed_endpoint_measures.2,
      Measure.map_prod_map _ _ hA hB]
  have hPush : ν.prod μψ = ((μa.prod μb).prod μψ).map T := by
    rw [hEP]
    simpa only [Measure.map_id] using Measure.map_prod_map (μa.prod μb) μψ hF measurable_id
  let R : Set (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) := (SA ×ˢ SB) ×ˢ Icc (-π) π
  have hRm : MeasurableSet R :=
    ((measurableSet_Icc.prod measurableSet_Icc).prod
      (measurableSet_Icc.prod measurableSet_Icc)).prod measurableSet_Icc
  have hrect : (μa.prod μb).prod μψ =
      (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ)).restrict R := by
    dsimp [μa,μb,μψ,R]
    rw [Measure.prod_restrict,Measure.prod_restrict]
    rfl
  let E : Chart5 ≃ᵐ (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) :=
    { toEquiv :=
      { toFun := fun y => (((y 0,y 1),(y 2,y 3)),y 4)
        invFun := fun z => pack5 z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2
        left_inv := by intro y; ext i; fin_cases i <;> simp [pack5]
        right_inv := by intro z; simp [pack5] }
      measurable_toFun := target_coordinates_preserving.measurable
      measurable_invFun := by
        change Measurable (fun z : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) =>
          pack5 z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)
        unfold pack5
        fun_prop }
  have hE : MeasurePreserving E := target_coordinates_preserving
  have htA : Measurable targetEndpointA := by
    change Measurable (fun y : Chart5 => targetEndpointA y)
    unfold targetEndpointA endpointCylinder
    fun_prop
  have htB : Measurable targetEndpointB := by
    change Measurable (fun y : Chart5 => targetEndpointB y)
    unfold targetEndpointB endpointCylinder
    fun_prop
  have hin : Measurable (fun y : Chart5 => ((targetEndpointA y,targetEndpointB y),y 4)) :=
    (htA.prodMk htB).prodMk (by fun_prop)
  have htc : Measurable targetCenter := by
    have hh : Measurable (fun y : Chart5 => D ((targetEndpointA y,targetEndpointB y),y 4)) :=
      hDm.comp hin
    exact hh
  have htargetm : MeasurableSet targetIncidence := by
    unfold targetIncidence
    measurability
  have hsame (y : Chart5) : R.indicator (fun z => M (T z)) (E y) =
      targetIncidence.indicator (targetTest G) y := by
    have hDc : D (T (E y)) = targetCenter y := rfl
    have hAc : (F (E y).1).1 = targetEndpointA y := rfl
    have hBc : (F (E y).1).2 = targetEndpointB y := rfl
    by_cases hr : E y ∈ R
    · rw [Set.indicator_of_mem hr]
      change (if (0 < dist (targetEndpointA y) (targetEndpointB y) ∧
        dist (targetEndpointA y) (targetEndpointB y) < 1) ∧ targetCenter y ∈ LamC
        then G (targetCenter y) (targetEndpointA y) (targetEndpointB y) /
          dist (targetEndpointA y) (targetEndpointB y) else 0) = _
      by_cases hi : (0 < dist (targetEndpointA y) (targetEndpointB y) ∧
        dist (targetEndpointA y) (targetEndpointB y) < 1) ∧ targetCenter y ∈ LamC
      · have hy : y ∈ targetIncidence := by
          rcases hr with ⟨⟨ha,hb⟩,hψ⟩
          exact ⟨ha.1,hb.1,ha.2,hb.2,hψ,hi.1.1,hi.1.2,hi.2⟩
        rw [if_pos hi,Set.indicator_of_mem hy]
        rfl
      · have hy : y ∉ targetIncidence := by
          intro hy
          exact hi ⟨⟨hy.2.2.2.2.2.1,hy.2.2.2.2.2.2.1⟩,hy.2.2.2.2.2.2.2⟩
        rw [if_neg hi,Set.indicator_of_notMem hy]
    · rw [Set.indicator_of_notMem hr]
      have hy : y ∉ targetIncidence := by
        intro hy
        apply hr
        exact ⟨⟨⟨hy.1,hy.2.2.1⟩,⟨hy.2.1,hy.2.2.2.1⟩⟩,hy.2.2.2.2.1⟩
      rw [Set.indicator_of_notMem hy]
  change (∫ p, ∫ q, J (p,q) ∂μB ∂μA) = _
  calc
    (∫ p, ∫ q, J (p,q) ∂μB ∂μA) = ∫ pq, J pq ∂ν := (integral_prod J hJi).symm
    _ = ∫ pq, ∫ ψ, M (pq,ψ) ∂μψ ∂ν := integral_congr_ae hJae
    _ = ∫ w, M w ∂(ν.prod μψ) := (integral_prod M hM).symm
    _ = ∫ z, M (T z) ∂((μa.prod μb).prod μψ) := by
      rw [hPush]
      exact integral_map hT.aemeasurable hMm.aestronglyMeasurable
    _ = ∫ z in R, M (T z) := by rw [hrect]
    _ = ∫ z, R.indicator (fun z => M (T z)) z := (integral_indicator hRm).symm
    _ = ∫ y : Chart5, R.indicator (fun z => M (T z)) (E y) := (hE.integral_comp' _).symm
    _ = ∫ y : Chart5, targetIncidence.indicator (targetTest G) y :=
      integral_congr_ae (Filter.Eventually.of_forall hsame)
    _ = ∫ y in targetIncidence, targetTest G y := integral_indicator htargetm
