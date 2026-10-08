import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_radialCone_eq
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem proof_SphereGeom_Aux_Cylinder_dOmega_normalize :
    dOmega = (3 : ENNReal) •
      (((volume : Measure E3).restrict (Metric.ball (0 : E3) 1 \ {0})).map
        (fun u : E3 => (‖u‖⁻¹ : ℝ) • u)) := by
  have hn : Measurable (fun u : E3 => (‖u‖⁻¹ : ℝ) • u) := by fun_prop
  have hc : Measurable (fun u : Metric.sphere (0 : E3) 1 => (0 : E3) + (u : E3)) := by fun_prop
  apply Measure.ext
  intro A hA
  unfold dOmega sphereMeasure
  rw [Measure.map_apply hc hA]
  simp only [zero_add]
  rw [Measure.toSphere_apply' _ (hA.preimage measurable_subtype_coe)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  change 3 * volume (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
    {u : Metric.sphere (0 : E3) 1 | (u : E3) ∈ A})) = _
  rw [SphereGeom.Aux.Cylinder.radialCone_eq A,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hn hA,
    Measure.restrict_apply (hA.preimage hn)]
  congr 2
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hlt, hA⟩
    exact ⟨hA, hlt, fun heq => by simp [heq] at hp⟩
  · rintro ⟨hA, hlt, hne⟩
    exact ⟨norm_pos_iff.mpr hne, hlt, hA⟩
