import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Archimedes_cone_volume_axis0_Iic
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem proof_SphereGeom_Aux_Archimedes_cone_volume_Iic (n : E3) (hn : ‖n‖ = 1) (h : ℝ) :
    (volume : Measure E3) (Set.Ioo (0 : ℝ) 1 •
      ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
        {u : Metric.sphere (0 : E3) 1 | inner ℝ n (u : E3) ≤ h})) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (min h 1 + 1)) := by
  let e : E3 := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_single]
  let R : E3 ≃ₗᵢ[ℝ] E3 := (Submodule.span ℝ {n-e})ᗮ.reflection
  have hRn : R n = e := Submodule.reflection_sub (hn.trans he.symm)
  let C (v : E3) : Set E3 := Set.Ioo (0 : ℝ) 1 •
    ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
      {u : Metric.sphere (0 : E3) 1 | inner ℝ v (u : E3) ≤ h})
  have hC : R ⁻¹' C e = C n := by
    ext x
    change R x ∈ C e ↔ x ∈ C n
    simp only [C, Set.mem_smul_set, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, hxy⟩
      refine ⟨r, hr, R.symm (u : E3), ?_, ?_⟩
      · refine ⟨⟨R.symm (u : E3), ?_⟩, ?_, rfl⟩
        · simpa [Metric.mem_sphere, dist_zero_right] using u.property
        · change inner ℝ n (R.symm (u : E3)) ≤ h
          rw [← R.inner_map_map n (R.symm (u : E3)), R.apply_symm_apply, hRn]
          exact hu
      · apply R.injective
        simpa using hxy
    · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, hxy⟩
      refine ⟨r, hr, R (u : E3), ?_, ?_⟩
      · refine ⟨⟨R (u : E3), ?_⟩, ?_, rfl⟩
        · simpa [Metric.mem_sphere, dist_zero_right] using u.property
        · simpa [← hRn] using (show inner ℝ n (u : E3) ≤ h from hu)
      · simpa using congrArg R hxy
  change volume (C n) = _
  rw [← hC, R.measurePreserving.measure_preimage_emb R.toHomeomorph.measurableEmbedding]
  exact SphereGeom.Aux.Archimedes.cone_volume_axis0_Iic h
