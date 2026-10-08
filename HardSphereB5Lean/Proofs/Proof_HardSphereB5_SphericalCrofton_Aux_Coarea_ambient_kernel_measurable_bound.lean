import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_A
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_B
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_inner_unit_distance
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_rational_remainder_bound
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_ambient_kernel_measurable_bound (f : Kern) :
  let G (D p p' : Pt) : ℝ := rhoK f (inner ℝ (p - D) (p' - D)) *
    inner ℝ (p - D) (NAv p p') * inner ℝ (p' - D) (NBv p p')
  Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2) ∧
    ∀ (D p p' : Pt), D ∈ LamC → p ∈ FA → p' ∈ FB →
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 →
      |G D p p'| ≤ 1 := by
  dsimp only
  constructor
  · have hI : Continuous (fun x : Pt × Pt × Pt =>
        inner ℝ (x.2.1 - x.1) (x.2.2 - x.1)) := by fun_prop
    have hA : Continuous (fun x : Pt × Pt × Pt =>
        inner ℝ (x.2.1 - x.1) (NAv x.2.1 x.2.2)) := by
      unfold NAv cross crossProduct
      fun_prop
    have hB : Continuous (fun x : Pt × Pt × Pt =>
        inner ℝ (x.2.2 - x.1) (NBv x.2.1 x.2.2)) := by
      unfold NBv cross crossProduct
      fun_prop
    have hρ : Measurable (rhoK f) := by
      cases f with
      | one =>
        change Measurable (fun x : ℝ => (1 - 2 * x) / (1 - x ^ 2))
        fun_prop
      | cos =>
        change Measurable (fun x : ℝ => (1/4 - x ^ 2) / (1 - x ^ 2))
        fun_prop
    exact ((hρ.comp hI.measurable).mul hA.measurable).mul hB.measurable
  · intro D p p' hD hp hp' hDp hDp' hd0 hd1
    have hu : ‖p - D‖ = 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hDp
    have hv : ‖p' - D‖ = 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hDp'
    have ha : ‖D‖ ≤ 1 := by
      simpa [LamC, Metric.mem_closedBall, dist_eq_norm] using hD.1
    have hb : ‖D - e‖ ≤ 1 := by
      simpa [LamC, Metric.mem_closedBall, dist_eq_norm] using hD.2
    have hInv (z : Pt) : |‖z‖⁻¹| * ‖z‖ ≤ 1 := by
      rw [abs_inv, abs_of_nonneg (norm_nonneg z)]
      by_cases hz : z = 0
      · simp [hz]
      · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
    have hnA : ‖nAv D‖ ≤ 1 := by
      simpa [nAv, norm_smul] using hInv D
    have hnB : ‖nBv D‖ ≤ 1 := by
      simpa [nBv, norm_smul, norm_sub_rev] using hInv (D-e)
    have huvDist : dist (p - D) (p' - D) = dist p p' := by
      simp only [dist_eq_norm]
      congr 1
      abel
    have hxEq : inner ℝ (p - D) (p' - D) = 1 - (dist p p') ^ 2 / 2 := by
      simpa only [huvDist] using
        HardSphereB5.SphericalCrofton.Aux.Coarea.inner_unit_distance (p-D) (p'-D) hu hv
    have hd2 : (dist p p') ^ 2 < 1 := by
      simpa [pow_two] using mul_self_lt_mul_self hd0.le hd1
    have hx : |inner ℝ (p-D) (p'-D)| ≤ 1 := by
      simpa only [hu, hv, one_mul] using abs_real_inner_le_norm (p-D) (p'-D)
    have hxlo := (abs_le.mp hx).1
    have hxhi := (abs_le.mp hx).2
    have hx0 : 0 ≤ inner ℝ (p-D) (p'-D) := by nlinarith [hxEq]
    have hq1 : |1 - 2 * inner ℝ (p-D) (p'-D)| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hq2 : |1/4 - inner ℝ (p-D) (p'-D) ^ 2| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (inner ℝ (p-D) (p'-D)),
        sq_nonneg (inner ℝ (p-D) (p'-D) - 1),
        sq_nonneg (inner ℝ (p-D) (p'-D) + 1)]
    have hnum : |rhoK f (inner ℝ (p-D) (p'-D)) *
        inner ℝ (nAv D) (cross (p-D) (p'-D)) *
        inner ℝ (nBv D) (cross (p-D) (p'-D))| ≤ 1 := by
      cases f with
      | one => exact (SphereGeom.Aux.Santalo.rational_remainder_bound
          (nAv D) (nBv D) (p-D) (p'-D) (1 - 2 * inner ℝ (p-D) (p'-D))
          hnA hnB hu hv).trans hq1
      | cos => exact (SphereGeom.Aux.Santalo.rational_remainder_bound
          (nAv D) (nBv D) (p-D) (p'-D) (1/4 - inner ℝ (p-D) (p'-D) ^ 2)
          hnA hnB hu hv).trans hq2
    have hcancelA : inner ℝ (p-D) (NAv p p') =
        ‖D‖ * inner ℝ (nAv D) (cross (p-D) (p'-D)) := by
      simpa using (HardSphereB5.SphericalCrofton.Aux.Coarea.normal_cancel_A D (p-D) (p'-D)).symm
    have hcancelB : inner ℝ (p'-D) (NBv p p') =
        ‖D-e‖ * inner ℝ (nBv D) (cross (p-D) (p'-D)) := by
      simpa using (HardSphereB5.SphericalCrofton.Aux.Coarea.normal_cancel_B D (p-D) (p'-D)).symm
    have hG : rhoK f (inner ℝ (p-D) (p'-D)) *
        inner ℝ (p-D) (NAv p p') * inner ℝ (p'-D) (NBv p p') =
        (‖D‖ * ‖D-e‖) * (rhoK f (inner ℝ (p-D) (p'-D)) *
          inner ℝ (nAv D) (cross (p-D) (p'-D)) *
          inner ℝ (nBv D) (cross (p-D) (p'-D))) := by
      rw [hcancelA, hcancelB]
      ring
    have hab : ‖D‖ * ‖D-e‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul ha hb (norm_nonneg (D-e)) (by norm_num : (0:ℝ) ≤ 1)
    rw [hG, abs_mul, abs_of_nonneg (mul_nonneg (norm_nonneg D) (norm_nonneg (D-e)))]
    simpa only [one_mul] using mul_le_mul hab hnum (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
