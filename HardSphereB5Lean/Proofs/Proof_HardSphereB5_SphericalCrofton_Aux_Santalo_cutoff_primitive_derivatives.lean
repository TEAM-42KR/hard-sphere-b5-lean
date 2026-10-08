import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_cutoff_order_two
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton Set Filter
open scoped Classical Topology

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_cutoff_primitive_derivatives (f : Kern) (d : ℝ) :
    HasDerivAt (fun x : ℝ => Pprim f (min x (π / 3))) (cutKern f d) d ∧
      HasDerivAt (cutKern f) (if d < π / 3 then deriv (phiK f) d else 0) d := by
  have hdiff : Differentiable ℝ (phiK f) := by
    intro x
    cases f with
    | one =>
      change DifferentiableAt ℝ (fun L : ℝ => L - 2 * Real.sin L + √3 - π / 3) x
      fun_prop
    | cos =>
      change DifferentiableAt ℝ (fun L : ℝ => π / 12 + √3 / 8 - L / 4 - Real.sin (2 * L) / 4) x
      fun_prop
  have hcont : Continuous (phiK f) := hdiff.continuous
  have hprim (x : ℝ) : HasDerivAt (Pprim f) (phiK f x) x := by
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 x)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hzero : phiK f (π / 3) = 0 := (HardSphereB5.SphericalCrofton.cutoff_order_two f).1
  have hdzero : deriv (phiK f) (π / 3) = 0 :=
    (HardSphereB5.SphericalCrofton.cutoff_order_two f).2.1
  rcases lt_trichotomy d (π / 3) with hd | rfl | hd
  · have heqP : (fun x : ℝ => Pprim f (min x (π / 3))) =ᶠ[𝓝 d] Pprim f := by
      filter_upwards [Iio_mem_nhds hd] with x hx
      change x < π / 3 at hx
      simp only [min_eq_left hx.le]
    have heqQ : cutKern f =ᶠ[𝓝 d] phiK f := by
      filter_upwards [Iio_mem_nhds hd] with x hx
      change x < π / 3 at hx
      simp only [cutKern, if_pos hx]
    refine ⟨?_, ?_⟩
    · simpa only [cutKern, if_pos hd] using (hprim d).congr_of_eventuallyEq heqP
    · simpa only [if_pos hd] using (hdiff d).hasDerivAt.congr_of_eventuallyEq heqQ
  · have hp0 : HasDerivAt (Pprim f) 0 (π / 3) :=
      (hprim (π / 3)).congr_deriv hzero
    have hq0 : HasDerivAt (phiK f) 0 (π / 3) :=
      (hdiff (π / 3)).hasDerivAt.congr_deriv hdzero
    have hpL : HasDerivWithinAt (fun x : ℝ => Pprim f (min x (π / 3)))
        0 (Iic (π / 3)) (π / 3) := by
      refine hp0.hasDerivWithinAt.congr_of_mem ?_ (by simp)
      intro x hx
      change x ≤ π / 3 at hx
      simp only [min_eq_left hx]
    have hpR : HasDerivWithinAt (fun x : ℝ => Pprim f (min x (π / 3)))
        0 (Ici (π / 3)) (π / 3) := by
      refine (hasDerivAt_const (π / 3) (Pprim f (π / 3))).hasDerivWithinAt.congr_of_mem
        ?_ (by simp)
      intro x hx
      change π / 3 ≤ x at hx
      simp only [min_eq_right hx]
    have hqL : HasDerivWithinAt (cutKern f) 0 (Iic (π / 3)) (π / 3) := by
      refine hq0.hasDerivWithinAt.congr_of_mem ?_ (by simp)
      intro x hx
      change x ≤ π / 3 at hx
      by_cases hlt : x < π / 3
      · simp only [cutKern, if_pos hlt]
      · have heq : x = π / 3 := le_antisymm hx (le_of_not_gt hlt)
        subst x
        simp [cutKern, hzero]
    have hqR : HasDerivWithinAt (cutKern f) 0 (Ici (π / 3)) (π / 3) := by
      refine (hasDerivAt_const (π / 3) (0 : ℝ)).hasDerivWithinAt.congr_of_mem
        ?_ (by simp)
      intro x hx
      change π / 3 ≤ x at hx
      simp only [cutKern, if_neg (not_lt.mpr hx)]
    have hp : HasDerivAt (fun x : ℝ => Pprim f (min x (π / 3))) 0 (π / 3) := by
      simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hpL.union hpR
    have hq : HasDerivAt (cutKern f) 0 (π / 3) := by
      simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hqL.union hqR
    exact ⟨by simpa [cutKern] using hp, by simpa using hq⟩
  · have heqP : (fun x : ℝ => Pprim f (min x (π / 3))) =ᶠ[𝓝 d]
        (fun _ : ℝ => Pprim f (π / 3)) := by
      filter_upwards [Ioi_mem_nhds hd] with x hx
      change π / 3 < x at hx
      simp only [min_eq_right hx.le]
    have heqQ : cutKern f =ᶠ[𝓝 d] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hd] with x hx
      change π / 3 < x at hx
      simp only [cutKern, if_neg (not_lt.mpr hx.le)]
    refine ⟨?_, ?_⟩
    · simpa only [cutKern, if_neg (not_lt.mpr hd.le)] using
        (hasDerivAt_const d (Pprim f (π / 3))).congr_of_eventuallyEq heqP
    · simpa only [if_neg (not_lt.mpr hd.le)] using
        (hasDerivAt_const d (0 : ℝ)).congr_of_eventuallyEq heqQ
