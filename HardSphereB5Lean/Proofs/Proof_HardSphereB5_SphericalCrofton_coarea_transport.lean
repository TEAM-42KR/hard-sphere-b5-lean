import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_transport
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_normalization
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_ambient_kernel_measurable_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_product
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_inner_unit_distance
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 1000000

theorem proof_HardSphereB5_SphericalCrofton_coarea_transport (f : Kern) :
    frakB f = ∫ p in FA, ∫ p' in FB,
      (if 0 < dist p p' ∧ dist p p' < 1 then
          rhoK f (1 - dist p p' ^ 2 / 2) / dist p p' * circInt p p' else 0)
        ∂(sphereMeasure e) ∂(sphereMeasure 0) := by
  let G (D p p' : Pt) : ℝ := rhoK f (inner ℝ (p-D) (p'-D)) *
    inner ℝ (p-D) (NAv p p') * inner ℝ (p'-D) (NBv p p')
  rcases Aux.Coarea.ambient_kernel_measurable_bound f with ⟨hG,hGb⟩
  have hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p=1 → dist D p'=1 → 0<dist p p' → dist p p'<1 → |G D p p'|≤1 := by
    intro D hD p hp p' hp'
    exact hGb D p p' hD hp hp'
  have hLam : MeasurableSet LamC := measurableSet_closedBall.inter measurableSet_closedBall
  have hArcA (D : Pt) : MeasurableSet (arcA D) := by
    dsimp [arcA,SigmaD,LamC]
    split_ifs <;> measurability
  have hArcB (D : Pt) : MeasurableSet (arcB D) := by
    dsimp [arcB,SigmaD,LamC]
    split_ifs <;> measurability
  have hsource : frakB f = ∫ D in LamC, ∫ u in arcA D, ∫ v in arcB D,
      (if 0 < dist (D+u) (D+v) ∧ dist (D+u) (D+v) < 1 then
        G D (D+u) (D+v) /
          (‖D‖ * ‖D-e‖ * Aux.MovingArc.rA D * Aux.MovingArc.rB D)
        else 0) ∂arcMeasure ∂arcMeasure := by
    apply setIntegral_congr_fun hLam
    intro D hD
    apply setIntegral_congr_fun (hArcA D)
    intro u hu
    apply setIntegral_congr_fun (hArcB D)
    intro v hv
    have hD0 : D≠0 := by intro hz; simpa [arcA,hz] using hu
    have hDe : D≠e := by intro hz; simpa [arcB,hz] using hv
    have huN : ‖u‖=1 := by
      have hh : u ∈ SigmaD D ∧ ‖D+u‖=1 := by simpa only [arcA,if_neg hD0,Set.mem_setOf_eq] using hu
      exact hh.1.1
    have hvN : ‖v‖=1 := by
      have hh : v ∈ SigmaD D ∧ dist (D+v) e=1 := by simpa only [arcB,if_neg hDe,Set.mem_setOf_eq] using hv
      exact hh.1.1
    have hx : inner ℝ u v=1-dist (D+u) (D+v)^2/2 := by
      rw [dist_add_left]
      exact Aux.Coarea.inner_unit_distance u v huN hvN
    have hsrc := Aux.Coarea.source_normalization f D u v hD hu hv
    rw [← hx] at hsrc
    simpa [G,Aux.MovingArc.rA,Aux.MovingArc.rB] using hsrc
  have htarget (p p' : Pt) :
      (if 0 < dist p p' ∧ dist p p' < 1 then (dist p p')⁻¹ *
          ∫ q in {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (p'-p) = 0 ∧
            midpoint ℝ p p' + √(1-dist p p'^2/4) • q ∈ LamC},
            G (midpoint ℝ p p' + √(1-dist p p'^2/4) • q) p p' ∂arcMeasure
          else 0) =
      (if 0 < dist p p' ∧ dist p p' < 1 then
          rhoK f (1 - dist p p' ^ 2 / 2) / dist p p' * circInt p p' else 0) := by
    by_cases hnear : 0<dist p p' ∧ dist p p'<1
    · rw [if_pos hnear,if_pos hnear]
      let r : ℝ := √(1-dist p p'^2/4)
      let S : Set Pt := {q : Pt | ‖q‖=1 ∧ inner ℝ q (p'-p)=0 ∧
        midpoint ℝ p p'+r•q ∈ LamC}
      have hS : MeasurableSet S := by dsimp [S,LamC]; measurability
      have heq : ∫ q in S, G (midpoint ℝ p p'+r•q) p p' ∂arcMeasure =
          rhoK f (1-dist p p'^2/2) * circInt p p' := by
        calc
          _ = ∫ q in S, rhoK f (1-dist p p'^2/2) *
              ((1-dist p p'^2/4)*inner ℝ q (NAv p p')*inner ℝ q (NBv p p')) ∂arcMeasure := by
            apply setIntegral_congr_fun hS
            intro q hq
            let D : Pt := midpoint ℝ p p'+r•q
            have hinc : dist D p=1 ∧ dist D p'=1 :=
              (Aux.Coarea.center_circle_iff p p' D (by linarith [hnear.2])).2
                ⟨q,hq.1,hq.2.1,rfl⟩
            have hu : ‖p-D‖=1 := by simpa only [dist_eq_norm,norm_sub_rev] using hinc.1
            have hv : ‖p'-D‖=1 := by simpa only [dist_eq_norm,norm_sub_rev] using hinc.2
            have hx : inner ℝ (p-D) (p'-D)=1-dist p p'^2/2 := by
              simpa only [dist_sub_right] using Aux.Coarea.inner_unit_distance (p-D) (p'-D) hu hv
            have hprod := Aux.Coarea.center_circle_product p p' D q r rfl
            have hr : r^2=1-dist p p'^2/4 := Real.sq_sqrt (by nlinarith [hnear.1,hnear.2])
            dsimp only [G]
            change rhoK f (inner ℝ (p-D) (p'-D)) * inner ℝ (p-D) (NAv p p') *
              inner ℝ (p'-D) (NBv p p') = _
            rw [hx, mul_assoc, hprod,hr]
          _ = rhoK f (1-dist p p'^2/2) * circInt p p' := integral_const_mul _ _
      rw [heq]
      ring
    · rw [if_neg hnear,if_neg hnear]
  calc
    frakB f = _ := hsource
    _ = _ := Aux.Coarea.incidence_transport G hG 1 (by norm_num) hbound
    _ = _ := by
      apply setIntegral_congr_fun (Metric.isClosed_sphere.measurableSet.inter measurableSet_closedBall)
      intro p hp
      apply setIntegral_congr_fun (Metric.isClosed_sphere.measurableSet.inter measurableSet_closedBall)
      intro p' hp'
      exact htarget p p'
