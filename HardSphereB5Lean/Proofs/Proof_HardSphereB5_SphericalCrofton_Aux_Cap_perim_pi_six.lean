import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_frontier_slice
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_sphere_slice_circle_image
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
set_option autoImplicit false

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Cap_perim_pi_six (n : Pt) (hn : ‖n‖ = 1) : perim (cap n (Real.cos (π / 6))) = π := by
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hc0 : 0 < Real.cos (π / 6) := by rw [Real.cos_pi_div_six]; positivity
  have hc1 : Real.cos (π / 6) < 1 := by rw [Real.cos_pi_div_six]; nlinarith
  have hcabs : |Real.cos (π / 6)| < 1 := by rw [abs_of_pos hc0]; exact hc1
  have hrad : Real.sqrt (1 - Real.cos (π / 6) ^ 2) = (1 / 2 : ℝ) := by
    rw [Real.cos_pi_div_six]
    have hx0 : 0 ≤ 1 - (Real.sqrt 3 / 2) ^ 2 := by nlinarith
    have hx2 := Real.sq_sqrt hx0
    have hx := Real.sqrt_nonneg (1 - (Real.sqrt 3 / 2) ^ 2)
    nlinarith
  obtain ⟨F₁, F₂, _, _, hF⟩ := SphereGeom.exists_measurable_frame
  let E : Fin 3 → E3 := ![F₁ n, F₂ n, n]
  have hE : Orthonormal ℝ E := hF n hn
  have hE2 : E 2 = n := rfl
  have he : Orthonormal ℝ (E ∘ (Fin.castSucc : Fin 2 → Fin 3)) :=
    hE.comp Fin.castSucc (Fin.castSucc_injective 2)
  have hfront : sFrontier (cap n (Real.cos (π / 6))) =
      circlePt (Real.cos (π / 6) • n) (E 0) (E 1) (1 / 2) '' Set.Icc (0 : ℝ) (2 * π) := by
    rw [HardSphereB5.SphericalCrofton.Aux.Cap.frontier_slice n hn _ hc0 hc1]
    simpa only [hE2, hrad] using
      (SphereGeom.Aux.sphere_slice_circle_image E hE (Real.cos (π / 6)) hcabs)
  have hArc := SphereGeom.arcMeasure_circle_arc (Real.cos (π / 6) • n)
    (E ∘ (Fin.castSucc : Fin 2 → Fin 3)) he (1 / 2) (by norm_num)
    0 (2 * π) (by positivity) (by simp)
  unfold perim len
  rw [hfront]
  change (arcMeasure (circlePt (Real.cos (π / 6) • n)
    ((E ∘ (Fin.castSucc : Fin 2 → Fin 3)) 0)
    ((E ∘ (Fin.castSucc : Fin 2 → Fin 3)) 1) (1 / 2) '' Set.Icc (0 : ℝ) (2 * π))).toReal = π
  rw [hArc]
  have hprod : (1 / 2 : ℝ) * (2 * π - 0) = π := by ring
  rw [hprod, ENNReal.toReal_ofReal Real.pi_pos.le]
