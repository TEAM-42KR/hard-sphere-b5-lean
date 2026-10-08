import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SupportCircles_support_poles_nonpositive_null
set_option autoImplicit false
open MeasureTheory Real SphereGeom
noncomputable section

theorem proof_SphereGeom_Aux_SupportCircles_support_poles_null (K : Set E3) (hK : K ⊆ Metric.sphere (0 : E3) 1) : dOmega {p : E3 | ‖p‖ = 1 ∧ ((∀ u ∈ K, inner ℝ p u ≤ 0) ∨ (∀ u ∈ K, 0 ≤ inner ℝ p u)) ∧ ∃ u ∈ K, inner ℝ p u = 0} = 0 := by
  let Kneg : Set E3 := (fun u : E3 => -u) '' K
  have hKneg : Kneg ⊆ Metric.sphere (0 : E3) 1 := by
    rintro v ⟨u, hu, rfl⟩
    have hn : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hK hu
    simpa [Metric.mem_sphere, dist_zero_right, norm_neg] using hn
  have hsub : {p : E3 | ‖p‖ = 1 ∧ ((∀ u ∈ K, inner ℝ p u ≤ 0) ∨ (∀ u ∈ K, 0 ≤ inner ℝ p u)) ∧ ∃ u ∈ K, inner ℝ p u = 0} ⊆
      {p : E3 | ‖p‖ = 1 ∧ (∀ u ∈ K, inner ℝ p u ≤ 0) ∧ ∃ u ∈ K, inner ℝ p u = 0} ∪
      {p : E3 | ‖p‖ = 1 ∧ (∀ u ∈ Kneg, inner ℝ p u ≤ 0) ∧ ∃ u ∈ Kneg, inner ℝ p u = 0} := by
    rintro p ⟨hp, hside, u, hu, hpu⟩
    rcases hside with hneg | hpos
    · left; exact ⟨hp, hneg, u, hu, hpu⟩
    · right
      refine ⟨hp, ?_, -u, ⟨u, hu, rfl⟩, ?_⟩
      · rintro v ⟨w, hw, rfl⟩
        simp only [inner_neg_right]
        exact neg_nonpos.mpr (hpos w hw)
      · simp [inner_neg_right, hpu]
  exact measure_mono_null hsub (measure_union_null
    (SphereGeom.Aux.SupportCircles.support_poles_nonpositive_null K hK)
    (SphereGeom.Aux.SupportCircles.support_poles_nonpositive_null Kneg hKneg))

