import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise
theorem proof_SphereGeom_dOmega_map_linearIsometryEquiv (R : E3 ≃ₗᵢ[ℝ] E3) : dOmega.map R = dOmega := by
  simp only [dOmega, sphereMeasure, zero_add]
  change (((volume : Measure E3).toSphere).map ((↑) : Metric.sphere (0 : E3) 1 → E3)).map R =
    ((volume : Measure E3).toSphere).map ((↑) : Metric.sphere (0 : E3) 1 → E3)
  ext s hs
  rw [Measure.map_apply R.continuous.measurable hs,
    Measure.map_apply measurable_subtype_coe (hs.preimage R.continuous.measurable),
    Measure.map_apply measurable_subtype_coe hs,
    Measure.toSphere_apply' _ ((hs.preimage R.continuous.measurable).preimage measurable_subtype_coe),
    Measure.toSphere_apply' _ (hs.preimage measurable_subtype_coe)]
  congr 1
  let A : Set E3 := (↑) '' (((↑) : Metric.sphere (0 : E3) 1 → E3) ⁻¹' s)
  let B : Set E3 := (↑) '' (((↑) : Metric.sphere (0 : E3) 1 → E3) ⁻¹' (R ⁻¹' s))
  have hcone : Set.Ioo (0 : ℝ) 1 • B = R ⁻¹' (Set.Ioo (0 : ℝ) 1 • A) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r, hr, R u, ⟨⟨R u, by simpa [Metric.mem_sphere, dist_zero_right] using u.property⟩, hu, rfl⟩,
        (R.map_smul r u).symm⟩
    · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, hx⟩
      refine ⟨r, hr, R.symm u, ⟨⟨R.symm u, by simpa [Metric.mem_sphere, dist_zero_right] using u.property⟩, ?_, rfl⟩, ?_⟩
      · simpa using hu
      · apply R.injective
        simpa using hx
  change volume (Set.Ioo (0 : ℝ) 1 • B) = volume (Set.Ioo (0 : ℝ) 1 • A)
  rw [hcone]
  exact R.measurePreserving.measure_preimage_emb R.toHomeomorph.measurableEmbedding _
