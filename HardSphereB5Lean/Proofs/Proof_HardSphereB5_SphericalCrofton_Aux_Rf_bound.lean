import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_cutKern_arccos_bound
import HardSphereB5Lean.Theorems.Thm_SphereGeom_gcIntegral_one
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Rf_bound (f : Kern) (K : Set Pt) :
    0 ≤ Rf f K ∧ Rf f K ≤ 12 * π := by
  haveI : IsFiniteMeasure dOmega := ⟨by rw [dOmega, SphereGeom.sphereMeasure_univ]; exact ENNReal.ofReal_lt_top⟩
  have hvalue (L : ℝ) : 0 ≤ (if 0 < L ∧ L < π / 3 then phiK f L else 0) ∧
      (if 0 < L ∧ L < π / 3 then phiK f L else 0) ≤ 6 := by
    by_cases h : 0 < L ∧ L < π / 3
    · have hπ : L ≤ π := by linarith [h.2, Real.pi_pos]
      have hh := Aux.cutKern_arccos_bound f (Real.cos L)
      rw [Real.arccos_cos (le_of_lt h.1) hπ] at hh
      simpa only [cutKern, if_pos h.2, if_pos h] using hh
    · simp [h]
  unfold Rf gcIntegral
  constructor
  · apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun p => (hvalue _).1)
  · by_cases hInt : Integrable (fun p : Pt => if 0 < chordLen K (greatCircle p) ∧ chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) dOmega
    · have hh := integral_mono_ae hInt (integrable_const (6 : ℝ)) (Filter.Eventually.of_forall (fun p => (hvalue (chordLen K (greatCircle p))).2))
      have hMass := SphereGeom.gcIntegral_one
      unfold gcIntegral at hMass
      have hSix : (∫ _ : Pt, (6 : ℝ) ∂dOmega) = 6 * ∫ _ : Pt, (1 : ℝ) ∂dOmega := by
        simpa only [mul_one] using (integral_const_mul (6 : ℝ) (fun _ : Pt => (1 : ℝ)))
      rw [hSix] at hh
      nlinarith [hMass]
    · rw [integral_undef hInt]
      simp
      positivity
