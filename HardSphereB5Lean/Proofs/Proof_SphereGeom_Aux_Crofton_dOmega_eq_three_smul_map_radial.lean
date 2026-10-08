import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem proof_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial : dOmega = (3 : ENNReal) •
    (volume.restrict (Metric.ball (0 : E3) 1)).map (fun x : E3 => ‖x‖⁻¹ • x) := by
  have hm : Measurable (fun x : E3 => ‖x‖⁻¹ • x) :=
    measurable_norm.inv.smul measurable_id
  apply Measure.ext
  intro S hS
  let T : Set (Metric.sphere (0 : E3) 1) := (Subtype.val) ⁻¹' S
  have hT : MeasurableSet T := measurable_subtype_coe hS
  have he : (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) '' T)) =
      ((fun x : E3 => ‖x‖⁻¹ • x) ⁻¹' S ∩ Metric.ball 0 1) \ {0} := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
      have hun : ‖(u : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using u.property
      have hnorm : ‖r • (u : E3)‖ = r := by simp [norm_smul, abs_of_pos hr.1, hun]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change ‖r • (u : E3)‖⁻¹ • (r • (u : E3)) ∈ S
        rw [hnorm, smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]
        exact hu
      · simpa [Metric.mem_ball, dist_zero_right, hnorm] using hr.2
      · change r • (u : E3) ≠ 0
        intro hz
        have hrz : r = 0 := by rw [hz, norm_zero] at hnorm; exact hnorm.symm
        exact hr.1.ne' hrz
    · rintro ⟨⟨hxS, hxb⟩, hx0⟩
      have hxne : x ≠ 0 := hx0
      have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hxne
      have hxlt : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hxb
      have hun : ‖(‖x‖⁻¹ • x)‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxp), inv_mul_cancel₀ hxp.ne']
      let u : Metric.sphere (0 : E3) 1 := ⟨‖x‖⁻¹ • x, by simpa [Metric.mem_sphere, dist_zero_right] using hun⟩
      refine ⟨‖x‖, ⟨hxp, hxlt⟩, (u : E3), ⟨u, hxS, rfl⟩, ?_⟩
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hxp.ne', one_smul]
  unfold dOmega sphereMeasure
  simp only [zero_add]
  rw [Measure.map_apply measurable_subtype_coe hS,
    Measure.toSphere_apply' volume hT]
  rw [he, measure_sdiff_null (measure_singleton (0 : E3))]
  rw [Measure.smul_apply, Measure.map_apply hm hS,
    Measure.restrict_apply (hm hS)]
  simp
