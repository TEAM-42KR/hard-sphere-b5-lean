import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_rational_remainder_bound
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

private theorem inv_norm_bound (z : Pt) : |‖z‖⁻¹| * ‖z‖ ≤ 1 := by
  rw [abs_inv, abs_of_nonneg (norm_nonneg z)]
  by_cases hz : z = 0
  · simp [hz]
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

private theorem lens_radii (D : Pt) (hD : D ∈ LamC) :
    (1/2 : ℝ) ≤ rA D ∧ (1/2 : ℝ) ≤ rB D := by
  have ha : ‖D‖ ≤ 1 := by simpa [LamC, Metric.mem_closedBall, dist_eq_norm] using hD.1
  have hb : ‖D-e‖ ≤ 1 := by simpa [LamC, Metric.mem_closedBall, dist_eq_norm] using hD.2
  have ha2 : ‖D‖^2 ≤ 1 := by nlinarith [norm_nonneg D]
  have hb2 : ‖D-e‖^2 ≤ 1 := by nlinarith [norm_nonneg (D-e)]
  have za : 0 ≤ 1 - ‖D‖^2 / 4 := by nlinarith
  have zb : 0 ≤ 1 - ‖D-e‖^2 / 4 := by nlinarith
  have sa : rA D ^ 2 = 1 - ‖D‖^2 / 4 := Real.sq_sqrt za
  have sb : rB D ^ 2 = 1 - ‖D-e‖^2 / 4 := Real.sq_sqrt zb
  have na : 0 ≤ rA D := Real.sqrt_nonneg _
  have nb : 0 ≤ rB D := Real.sqrt_nonneg _
  constructor <;> nlinarith

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_bKernel_uniform_bound (f : Kern) (D p q : Pt) (hD : D ∈ LamC)
    (hp : p ∈ arcA D) (hq : q ∈ arcB D) : ‖bKernel f D p q‖ ≤ 4 := by
  have hup : ‖p‖ = 1 := by
    by_cases hzero : D = 0
    · simp [arcA, hzero] at hp
    · simp only [arcA, hzero, if_false, Set.mem_setOf_eq] at hp
      exact hp.1.1
  have hvq : ‖q‖ = 1 := by
    by_cases hzero : D = e
    · simp [arcB, hzero] at hq
    · simp only [arcB, hzero, if_false, Set.mem_setOf_eq] at hq
      exact hq.1.1
  have hnA : ‖nAv D‖ ≤ 1 := by
    simpa [nAv, norm_smul] using inv_norm_bound D
  have hnB : ‖nBv D‖ ≤ 1 := by
    simpa [nBv, norm_smul, norm_sub_rev] using inv_norm_bound (D-e)
  obtain ⟨ha, hb⟩ := lens_radii D hD
  have hden : 0 < rA D * rB D := mul_pos (by linarith) (by linarith)
  have hden4 : (1/4 : ℝ) ≤ rA D * rB D := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hx : |inner ℝ p q| ≤ 1 := by simpa [hup, hvq] using abs_real_inner_le_norm p q
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  unfold bKernel
  by_cases hcut : (1/2 : ℝ) < inner ℝ p q
  · simp only [if_pos hcut, Real.norm_eq_abs, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    have hq1 : |1 - 2 * inner ℝ p q| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hq2 : |1/4 - inner ℝ p q ^ 2| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (inner ℝ p q), sq_nonneg (inner ℝ p q - 1), sq_nonneg (inner ℝ p q + 1)]
    have hnum : |rhoK f (inner ℝ p q) * inner ℝ (nAv D) (cross p q) * inner ℝ (nBv D) (cross p q)| ≤ 1 := by
      cases f with
      | one => exact (SphereGeom.Aux.Santalo.rational_remainder_bound (nAv D) (nBv D) p q
          (1 - 2 * inner ℝ p q) hnA hnB hup hvq).trans hq1
      | cos => exact (SphereGeom.Aux.Santalo.rational_remainder_bound (nAv D) (nBv D) p q
          (1/4 - inner ℝ p q ^ 2) hnA hnB hup hvq).trans hq2
    linarith
  · simp only [if_neg hcut, zero_div, norm_zero]
    norm_num
