import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_encard_Psi_fiber_eq
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option backward.isDefEq.respectTransparency false in
theorem proof_SphereGeom_Aux_Crofton_lintegral_count_eq_three_radial_fibers (γ a b : ℝ → E3) (S : Set ℝ)
    (hs : ∀ s ∈ S, ‖γ s‖ = 1) (hinj : Set.InjOn γ S)
    (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, γ s] ∧ cross (a s) (b s) = γ s)
    (hN : Measurable (fun p : E3 => ((greatCircle p ∩ γ '' S).encard : ENNReal))) :
    let Ψ : E3 → E3 := fun y => y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))
    let D : Set E3 := {y | y 0 ∈ S ∧ y 1 ∈ Set.Ioc 0 (2 * Real.pi) ∧ y 2 ∈ Set.Ioo 0 1}
    (∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega) =
      3 * ∫⁻ x, ((D ∩ Ψ ⁻¹' {x}).encard : ENNReal) := by
  classical
  let Ψ : E3 → E3 := fun y => y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))
  let D : Set E3 := {y | y 0 ∈ S ∧ y 1 ∈ Set.Ioc 0 (2 * Real.pi) ∧ y 2 ∈ Set.Ioo 0 1}
  let F : E3 → ENNReal := fun x => ((D ∩ Ψ ⁻¹' {x}).encard : ENNReal)
  change _ = 3 * ∫⁻ x, F x
  have hcount (p : E3) : (greatCircle p ∩ γ '' S).encard =
      {s : ℝ | s ∈ S ∧ inner ℝ p (γ s) = 0}.encard := by
    have he : greatCircle p ∩ γ '' S = γ '' {s : ℝ | s ∈ S ∧ inner ℝ p (γ s) = 0} := by
      ext u
      constructor
      · rintro ⟨hu, s, hss, rfl⟩
        exact ⟨s, ⟨hss, hu.2⟩, rfl⟩
      · rintro ⟨s, ⟨hss, hp⟩, rfl⟩
        exact ⟨⟨hs s hss, hp⟩, ⟨s, hss, rfl⟩⟩
    rw [he]
    exact (hinj.mono (fun s h => h.1)).encard_image
  have hunit (s : ℝ) (hss : s ∈ S) (θ : ℝ) :
      ‖Real.cos θ • a s + Real.sin θ • b s‖ = 1 := by
    have hon := (hframe s hss).1
    have h00 : inner ℝ (a s) (a s) = 1 := by simpa using (orthonormal_iff_ite.mp hon) (0 : Fin 3) 0
    have h01 : inner ℝ (a s) (b s) = 0 := by simpa using (orthonormal_iff_ite.mp hon) (0 : Fin 3) 1
    have h10 : inner ℝ (b s) (a s) = 0 := by simpa using (orthonormal_iff_ite.mp hon) (1 : Fin 3) 0
    have h11 : inner ℝ (b s) (b s) = 1 := by simpa using (orthonormal_iff_ite.mp hon) (1 : Fin 3) 1
    have hsq : ‖Real.cos θ • a s + Real.sin θ • b s‖ ^ 2 = (1 : ℝ) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        h00, h01, h10, h11, mul_one, mul_zero, add_zero, zero_add]
      nlinarith [Real.cos_sq_add_sin_sq θ]
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp hsq
  have hsupport : Function.support F ⊆ Metric.ball (0 : E3) 1 := by
    intro x hx
    by_contra hxb
    apply hx
    have he : D ∩ Ψ ⁻¹' {x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hyx : Ψ y = x := hy.2
      have hnorm : ‖x‖ = y 2 := by
        rw [← hyx]
        simp only [Ψ, norm_smul, hunit (y 0) hy.1.1 (y 1), mul_one,
          Real.norm_eq_abs, abs_of_pos hy.1.2.2.1]
      exact hxb (by simpa [Metric.mem_ball, dist_zero_right, hnorm] using hy.1.2.2.2)
    simp [F, he]
  rw [SphereGeom.Aux.Crofton.dOmega_eq_three_smul_map_radial, lintegral_smul_measure]
  have hmrad : Measurable (fun x : E3 => ‖x‖⁻¹ • x) := measurable_norm.inv.smul measurable_id
  rw [lintegral_map hN hmrad]
  change 3 * (∫⁻ x in Metric.ball (0 : E3) 1,
    ((greatCircle (‖x‖⁻¹ • x) ∩ γ '' S).encard : ENNReal)) = 3 * ∫⁻ x, F x
  congr 1
  rw [← setLIntegral_eq_of_support_subset hsupport]
  apply lintegral_congr_ae
  have hnz : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E3) 1)), x ≠ 0 := by
    have h : ∀ᵐ x : E3 ∂volume, x ≠ 0 := by
      rw [ae_iff]
      have he : {x : E3 | ¬ x ≠ 0} = {0} := by ext x; simp
      rw [he]; simp
    exact h.filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem measurableSet_ball, hnz] with x hx hx0
  have hxn : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  rw [hcount]
  have hset : {s : ℝ | s ∈ S ∧ inner ℝ (‖x‖⁻¹ • x) (γ s) = 0} =
      {s : ℝ | s ∈ S ∧ inner ℝ x (γ s) = 0} := by
    ext s
    simp only [Set.mem_setOf_eq, real_inner_smul_left]
    have hinv : ‖x‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hx0)
    simp [mul_eq_zero, hinv]
  rw [hset]
  exact congrArg (fun z : ℕ∞ => (z : ENNReal))
    (SphereGeom.Aux.Crofton.encard_Psi_fiber_eq a b γ S hframe x hx0 hxn).symm
