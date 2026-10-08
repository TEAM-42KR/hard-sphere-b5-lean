import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section
open MeasureTheory Real
open scoped Classical Topology

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_volume_continuous_of_deps : Continuous (fun c : Fin 4 → Pt => vol c Finset.univ) := by
  classical
  have hm (d : Fin 4 → Pt) : MeasurableSet (body d Finset.univ) := by
    unfold body
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => measurableSet_closedBall
  have heq (d : Fin 4 → Pt) :
      vol d Finset.univ = ∫ x : Pt, (body d Finset.univ).indicator (fun _ => (1 : ℝ)) x := by
    simpa [vol, measureReal_def] using (integral_indicator_const (μ := volume) (1 : ℝ) (hm d)).symm
  simp_rw [heq]
  refine continuous_iff_continuousAt.mpr fun c => ?_
  apply continuousAt_of_dominated
    (bound := (Metric.closedBall (c 0) 2).indicator (fun _ : Pt => (1 : ℝ)))
  · exact Filter.Eventually.of_forall fun d => aestronglyMeasurable_const.indicator (hm d)
  · have hdist : ContinuousAt (fun d : Fin 4 → Pt => dist (d 0) (c 0)) c :=
      ((continuous_apply 0).dist continuous_const).continuousAt
    have hnear : ∀ᶠ d in 𝓝 c, dist (d 0) (c 0) < 1 :=
      hdist.eventually_lt continuousAt_const (by simp)
    filter_upwards [hnear] with d hd
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ body d Finset.univ
    · have hxd : x ∈ Metric.closedBall (d 0) 1 :=
        Set.mem_iInter.mp (Set.mem_iInter.mp hx 0) (Finset.mem_univ 0)
      have hxb : x ∈ Metric.closedBall (c 0) 2 := by
        apply Metric.mem_closedBall.mpr
        calc
          dist x (c 0) ≤ dist x (d 0) + dist (d 0) (c 0) := dist_triangle _ _ _
          _ ≤ 2 := by linarith [Metric.mem_closedBall.mp hxd]
      simp [hx, hxb]
    · by_cases hxb : x ∈ Metric.closedBall (c 0) 2 <;> simp [hx, hxb]
  · exact (integrableOn_const
      (μ := (volume : Measure Pt)) (s := Metric.closedBall (c 0) 2) (C := (1 : ℝ))
      (isCompact_closedBall (c 0) 2).measure_ne_top).integrable_indicator measurableSet_closedBall
  · have havoid : ∀ᵐ x ∂(volume : Measure Pt), ∀ i : Fin 4, dist x (c i) ≠ 1 := by
      apply ae_all_iff.mpr
      intro i
      have hz : volume (Metric.sphere (c i) 1) = 0 := Measure.addHaar_sphere volume (c i) 1
      have hn : ∀ᵐ x ∂(volume : Measure Pt), x ∉ Metric.sphere (c i) 1 := by
        rw [ae_iff]
        simpa only [not_not, Set.ofPred_mem_eq] using hz
      simpa only [Metric.mem_sphere] using hn
    filter_upwards [havoid] with x hx
    have hstable (i : Fin 4) : ∀ᶠ d in 𝓝 c,
        (dist x (d i) ≤ 1 ↔ dist x (c i) ≤ 1) := by
      have hdi : ContinuousAt (fun d : Fin 4 → Pt => dist x (d i)) c :=
        (continuous_const.dist (continuous_apply i)).continuousAt
      rcases lt_or_gt_of_ne (hx i) with hi | hi
      · filter_upwards [hdi.eventually_lt continuousAt_const hi] with d hd
        exact ⟨fun _ => hi.le, fun _ => hd.le⟩
      · filter_upwards [continuousAt_const.eventually_lt hdi hi] with d hd
        exact ⟨fun he => (not_le_of_gt hd he).elim,
          fun he => (not_le_of_gt hi he).elim⟩
    have hmem : ∀ᶠ d in 𝓝 c, x ∈ body d Finset.univ ↔ x ∈ body c Finset.univ := by
      filter_upwards [Filter.eventually_all.mpr hstable] with d hd
      simp only [body, Set.mem_iInter, Finset.mem_univ, forall_const, Metric.mem_closedBall]
      exact forall_congr' hd
    have hind : (fun _ : Fin 4 → Pt =>
        (body c Finset.univ).indicator (fun _ => (1 : ℝ)) x) =ᶠ[𝓝 c]
        (fun d => (body d Finset.univ).indicator (fun _ => (1 : ℝ)) x) := by
      filter_upwards [hmem] with d hd
      by_cases hc : x ∈ body c Finset.univ
      · simp [hc, hd.mpr hc]
      · have hdc : x ∉ body d Finset.univ := fun h => hc (hd.mp h)
        simp [hc, hdc]
    exact tendsto_const_nhds.congr' hind

end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_volume_continuous : Continuous (fun c : Fin 4 → Pt => vol c Finset.univ) := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_volume_continuous_of_deps

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_volume_continuous
