import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SupportCircles_cone_frontier_null
set_option autoImplicit false
open MeasureTheory Real SphereGeom
noncomputable section

theorem proof_SphereGeom_Aux_SupportCircles_support_poles_nonpositive_null (K : Set E3) (hK : K ⊆ Metric.sphere (0 : E3) 1) : dOmega {p : E3 | ‖p‖ = 1 ∧ (∀ u ∈ K, inner ℝ p u ≤ 0) ∧ ∃ u ∈ K, inner ℝ p u = 0} = 0 := by
  let C : Set E3 := {p | ∀ u ∈ K, inner ℝ p u ≤ 0}
  have hC : Convex ℝ C := by
    intro p hp q hq a b ha hb hab
    intro u hu
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hp u hu))
      (mul_nonpos_of_nonneg_of_nonpos hb (hq u hu))
  have hcone : ∀ r : ℝ, 0 < r → (fun x : E3 => r • x) ⁻¹' C = C := by
    intro r hr
    ext x
    change (∀ u ∈ K, inner ℝ (r • x) u ≤ 0) ↔ (∀ u ∈ K, inner ℝ x u ≤ 0)
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    constructor
    · intro hx u hu
      by_contra hbad
      have hpos : 0 < inner ℝ x u := lt_of_not_ge hbad
      exact (not_lt_of_ge (hx u hu)) (mul_pos hr hpos)
    · intro hx u hu
      exact mul_nonpos_of_nonneg_of_nonpos hr.le (hx u hu)
  have hsub : {p : E3 | ‖p‖ = 1 ∧ (∀ u ∈ K, inner ℝ p u ≤ 0) ∧ ∃ u ∈ K, inner ℝ p u = 0} ⊆ frontier C := by
    rintro p ⟨hp, hpC, u, hu, hpu⟩
    have hun : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hK hu
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hpC, Metric.mem_closure_iff.mpr ?_⟩
    intro ε hε
    refine ⟨p + (ε / 2) • u, ?_, ?_⟩
    · change ¬ (∀ v ∈ K, inner ℝ (p + (ε / 2) • u) v ≤ 0)
      intro hh
      have hh0 := hh u hu
      simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
        hpu, real_inner_self_eq_norm_sq, hun] at hh0
      norm_num at hh0
      linarith
    · have hd : dist p (p + (ε / 2) • u) = ε / 2 := by
        rw [dist_comm, dist_eq_norm]
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε), hun] <;> linarith
      simpa only [hd, dist_comm] using half_lt_self hε
  exact measure_mono_null hsub (SphereGeom.Aux.SupportCircles.cone_frontier_null C hC hcone)

