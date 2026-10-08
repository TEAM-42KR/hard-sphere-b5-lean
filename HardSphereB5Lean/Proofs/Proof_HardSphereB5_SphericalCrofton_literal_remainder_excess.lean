import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_hit_mass
import HardSphereB5Lean.Theorems.Thm_SphereGeom_gcIntegral_one
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_kernel_split
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_terms
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_literal_remainder_excess {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern) :
    RfAll f K = Rf f K + bK f * (2 * π - perim K) := by
  haveI : IsFiniteMeasure dOmega := ⟨by
    rw [dOmega, SphereGeom.sphereMeasure_univ]; exact ENNReal.ofReal_lt_top⟩
  have hπ3 : (0 : ℝ) < π / 3 := by positivity
  have hφ0 : phiK f 0 = bK f := by
    have h := kernel_split f 0 (by norm_num) (by positivity)
    have hk0 : kK f 0 = 0 := by simp [kK, min_eq_left (le_of_lt hπ3)]
    rw [hk0] at h
    simp only [mul_zero, zero_sub, if_pos hπ3] at h
    linarith
  have hpoint (p : Pt) :
      (if chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) =
      (if 0 < chordLen K (greatCircle p) ∧ chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) +
        bK f * ((1 : ℝ) - if 0 < chordLen K (greatCircle p) then 1 else 0) := by
    by_cases hpos : 0 < chordLen K (greatCircle p)
    · by_cases hcut : chordLen K (greatCircle p) < π / 3 <;> simp [hpos, hcut]
    · have hz : chordLen K (greatCircle p) = 0 := le_antisymm (le_of_not_gt hpos) ENNReal.toReal_nonneg
      simp [hz, hπ3, hφ0]
  obtain ⟨_, hH, hS, _⟩ := Aux.Chord.integrable_terms K hK.isCompact.measurableSet f
  have hOne : Integrable (fun _ : Pt => (1 : ℝ)) dOmega := integrable_const 1
  have hAdd := integral_add hS ((hOne.sub hH).const_mul (bK f))
  have hSub := integral_sub hOne hH
  simp only [Pi.add_apply, Pi.sub_apply] at hAdd hSub
  have hHit := hit_mass hK
  have hMass := SphereGeom.gcIntegral_one
  unfold gcIntegral at hHit hMass
  unfold RfAll Rf gcIntegral
  rw [show (fun p : Pt => if chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) =
      (fun p : Pt => (if 0 < chordLen K (greatCircle p) ∧ chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) + bK f * ((1 : ℝ) - if 0 < chordLen K (greatCircle p) then 1 else 0)) from funext hpoint]
  rw [hAdd, integral_const_mul, hSub]
  linear_combination (bK f) * hMass - (bK f) * hHit
