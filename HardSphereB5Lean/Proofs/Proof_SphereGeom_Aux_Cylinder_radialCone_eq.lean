import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem proof_SphereGeom_Aux_Cylinder_radialCone_eq (A : Set E3) :
    Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
      {u : Metric.sphere (0 : E3) 1 | (u : E3) ∈ A}) =
      {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ (‖x‖⁻¹ : ℝ) • x ∈ A} := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    have hn : ‖(u : E3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    have hnr : ‖r • (u : E3)‖ = r := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hn, mul_one]
    refine ⟨by simpa only [hnr] using hr.1, by simpa only [hnr] using hr.2, ?_⟩
    change (u : E3) ∈ A at hu
    rwa [hnr, smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]
  · rintro ⟨hx0, hx1, hxc⟩
    let u : E3 := ‖x‖⁻¹ • x
    have hn : ‖u‖ = 1 := by
      simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx0,
        inv_mul_cancel₀ hx0.ne']
    refine ⟨‖x‖, ⟨hx0, hx1⟩, u, ?_, ?_⟩
    · exact ⟨⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩, hxc, rfl⟩
    · simp only [u, smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]
