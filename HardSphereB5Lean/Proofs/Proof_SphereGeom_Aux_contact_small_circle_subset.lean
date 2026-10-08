import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_sphere_slice_circle_image
set_option autoImplicit false
open MeasureTheory Real SphereGeom
noncomputable section
theorem proof_SphereGeom_Aux_contact_small_circle_subset (q : E3) (hbound : ‖q‖ ≤ 1)
(h0 : q ≠ 0) (E : Fin 3 → E3) (hE : Orthonormal ℝ E) (hn : E 2 = ‖q‖⁻¹ • (-q)) :
{u : E3 | ‖u‖ = 1 ∧ ‖q + u‖ = 1} ⊆
circlePt ((-(1 / 2 : ℝ)) • q) (E 0) (E 1) (Real.sqrt (1 - ‖q‖ ^ 2 / 4)) ''
Set.Icc (0 : ℝ) (2 * π)  := by
  have hane : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hz : |‖q‖ / 2| < 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hcenter : (‖q‖ / 2) • E 2 = (-(1 / 2 : ℝ)) • q := by
    rw [hn, smul_smul, smul_neg, neg_smul]
    congr 1
    field_simp
  have hrEq : Real.sqrt (1 - (‖q‖ / 2) ^ 2) = Real.sqrt (1 - ‖q‖ ^ 2 / 4) := by
    congr 1
    ring
  intro u hu
  have hdinner : inner ℝ q u = -‖q‖ ^ 2 / 2 := by
    have hsum := norm_add_sq_real q u
    rw [hu.2, hu.1] at hsum
    nlinarith
  have hninner : inner ℝ (E 2) u = ‖q‖ / 2 := by
    rw [hn, real_inner_smul_left, inner_neg_left, hdinner]
    field_simp
  have hum : u ∈ {u : E3 | ‖u‖ = 1 ∧ inner ℝ (E 2) u = ‖q‖ / 2} := ⟨hu.1, hninner⟩
  rw [SphereGeom.Aux.sphere_slice_circle_image E hE (‖q‖ / 2) hz] at hum
  simpa only [hcenter, hrEq] using hum
