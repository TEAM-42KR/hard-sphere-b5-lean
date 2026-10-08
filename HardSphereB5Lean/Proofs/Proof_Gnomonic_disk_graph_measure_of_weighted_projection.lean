import HardSphereB5Lean.Definitions.Def_Gnomonic_unitDisk
set_option autoImplicit false
noncomputable section
open MeasureTheory SphereGeom Gnomonic
open scoped ENNReal RealInnerProductSpace
private theorem p6disk_map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (P : α → β) (g : β → ℝ≥0∞)
    (hP : Measurable P) (hg : Measurable g) :
    Measure.map P (μ.withDensity (fun x => g (P x))) =
      (Measure.map P μ).withDensity g := by
  ext1 s hs
  rw [Measure.map_apply hP hs, withDensity_apply _ (hs.preimage hP),
    withDensity_apply _ hs, setLIntegral_map hs hg hP]

private theorem p6disk_inverse_weight_transport {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (P : α → β) (U : β → α)
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (hP : Measurable P) (hU : Measurable U)
    (hf : Measurable f) (hg : Measurable g)
    (hpush : Measure.map P (μ.withDensity f) = ν)
    (hinverse : ∀ᵐ x ∂μ, U (P x) = x)
    (hcancel : ∀ᵐ x ∂μ, f x * g (P x) = 1) :
    Measure.map U (ν.withDensity g) = μ := by
  rw [← hpush, ← p6disk_map_withDensity_comp (μ.withDensity f) P g hP hg,
    Measure.map_map hU hP]
  have hgp : Measurable (fun x => g (P x)) := hg.comp hP
  rw [← withDensity_mul μ hf hgp]
  have hd : μ.withDensity (f * (fun x => g (P x))) = μ := by
    change μ.withDensity (fun x => f x * g (P x)) = μ
    rw [withDensity_congr_ae hcancel]
    exact withDensity_one
  rw [hd]
  exact (Measure.map_congr hinverse).trans Measure.map_id

private lemma p6disk_measurable_planeProjection : Measurable planeProjection := by
  unfold planeProjection
  fun_prop

private lemma p6disk_continuous_upperGraph : Continuous upperGraph := by
  unfold upperGraph
  fun_prop

private lemma p6disk_measurable_graphDensity : Measurable graphDensity := by
  unfold graphDensity
  fun_prop

private lemma p6disk_planeProjection_upperGraph (y : ℝ × ℝ) : planeProjection (upperGraph y) = y := by
  simp [planeProjection, upperGraph]

private lemma p6disk_unit_sphere_coords (u : E3) (hu : ‖u‖ = 1) :
    (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 = 1 := by
  simpa [Fin.sum_univ_three, hu, add_assoc] using (EuclideanSpace.real_norm_sq_eq u).symm

private lemma p6disk_upperGraph_inverse (u : E3) (hu : ‖u‖ = 1) (hp : 0 < u 2) :
    upperGraph (planeProjection u) = u := by
  have he : 1 - (u 0) ^ 2 - (u 1) ^ 2 = (u 2) ^ 2 := by
    linarith [p6disk_unit_sphere_coords u hu]
  have hs : Real.sqrt (1 - (u 0) ^ 2 - (u 1) ^ 2) = u 2 := by
    rw [he, Real.sqrt_sq (le_of_lt hp)]
  ext i
  fin_cases i <;> simp [upperGraph, planeProjection, hs]

private lemma p6disk_graphDensity_height_cancel (u : E3) (hu : ‖u‖ = 1) (hp : 0 < u 2) :
    ENNReal.ofReal (u 2) * graphDensity (planeProjection u) = 1 := by
  have he : 1 - (u 0) ^ 2 - (u 1) ^ 2 = (u 2) ^ 2 := by
    linarith [p6disk_unit_sphere_coords u hu]
  have hs : Real.sqrt (1 - (u 0) ^ 2 - (u 1) ^ 2) = u 2 := by
    rw [he, Real.sqrt_sq (le_of_lt hp)]
  change ENNReal.ofReal (u 2) * ENNReal.ofReal
    ((Real.sqrt (1 - (u 0) ^ 2 - (u 1) ^ 2))⁻¹) = 1
  rw [hs, ← ENNReal.ofReal_mul (le_of_lt hp), mul_inv_cancel₀ (ne_of_gt hp)]
  norm_num

private lemma p6disk_dOmega_ae_unit : ∀ᵐ u ∂dOmega, ‖u‖ = 1 := by
  rw [dOmega, sphereMeasure]
  have hm : Measurable (fun u : Metric.sphere (0 : E3) 1 => (0 : E3) + (u : E3)) := by
    fun_prop
  apply (ae_map_iff hm.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).2
  filter_upwards [] with u
  simpa [Metric.mem_sphere, dist_eq_norm] using u.property

private lemma p6disk_restrict_upperHemisphere :
    dOmega.restrict {u : E3 | 0 < u 2} = dOmega.restrict upperHemisphere := by
  apply Measure.restrict_congr_set
  filter_upwards [p6disk_dOmega_ae_unit] with u hu
  change (0 < u 2) = (‖u‖ = 1 ∧ 0 < u 2)
  simp [hu]

theorem proof_Gnomonic_disk_graph_measure_of_weighted_projection
    (hprojection :
      Measure.map planeProjection
        ((dOmega.restrict {u : E3 | 0 < u 2}).withDensity (fun u => ENNReal.ofReal (u 2))) =
        (volume : Measure (ℝ × ℝ)).restrict unitDisk) :
    Measure.map upperGraph
      (((volume : Measure (ℝ × ℝ)).restrict unitDisk).withDensity graphDensity) =
      dOmega.restrict upperHemisphere := by
  let μ : Measure E3 := dOmega.restrict {u : E3 | 0 < u 2}
  have hH : MeasurableSet {u : E3 | 0 < u 2} := by
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hn : ∀ᵐ u ∂μ, ‖u‖ = 1 := ae_restrict_of_ae p6disk_dOmega_ae_unit
  have hp : ∀ᵐ u ∂μ, 0 < u 2 := ae_restrict_mem hH
  have hi : ∀ᵐ u ∂μ, upperGraph (planeProjection u) = u := by
    filter_upwards [hn, hp] with u hun hup
    exact p6disk_upperGraph_inverse u hun hup
  have hc : ∀ᵐ u ∂μ, ENNReal.ofReal (u 2) * graphDensity (planeProjection u) = 1 := by
    filter_upwards [hn, hp] with u hun hup
    exact p6disk_graphDensity_height_cancel u hun hup
  have hm : Measurable (fun u : E3 => ENNReal.ofReal (u 2)) := by fun_prop
  have ht := p6disk_inverse_weight_transport μ ((volume : Measure (ℝ × ℝ)).restrict unitDisk)
    planeProjection upperGraph (fun u => ENNReal.ofReal (u 2)) graphDensity
    p6disk_measurable_planeProjection p6disk_continuous_upperGraph.measurable hm p6disk_measurable_graphDensity
    hprojection hi hc
  exact ht.trans p6disk_restrict_upperHemisphere
