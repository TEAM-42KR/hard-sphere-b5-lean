import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_chord_representation
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_chord_length_integral
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_hit_mass
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_kernel_split
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_kernel_constants
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_chordLen_le_pi_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_terms
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_crofton_decomposition {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern) :
    Ff f K = cA f * sArea K - cP f * perim K + Rf f K := by
  have hpoint : ∀ᵐ p ∂dOmega,
      (if 0 < chordLen K (greatCircle p) then kK f (chordLen K (greatCircle p)) else 0) =
      (alphaK f * (if 0 < chordLen K (greatCircle p) then chordLen K (greatCircle p) else 0) -
       bK f * (if 0 < chordLen K (greatCircle p) then (1 : ℝ) else 0)) +
       (if 0 < chordLen K (greatCircle p) ∧ chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) := by
    filter_upwards [Aux.Chord.chordLen_le_pi_ae hK] with p hp
    have h0 : 0 ≤ chordLen K (greatCircle p) := ENNReal.toReal_nonneg
    by_cases hpos : 0 < chordLen K (greatCircle p)
    · have hk := kernel_split f _ h0 hp
      by_cases hcut : chordLen K (greatCircle p) < π / 3
      · simpa [hpos, hcut] using hk
      · simpa [hpos, hcut] using hk
    · simp [hpos]
  obtain ⟨hL, hH, hS, _⟩ := Aux.Chord.integrable_terms K hK.isCompact.measurableSet f
  have hAdd := integral_add ((hL.const_mul (alphaK f)).sub (hH.const_mul (bK f))) hS
  have hSub := integral_sub (hL.const_mul (alphaK f)) (hH.const_mul (bK f))
  simp only [Pi.add_apply, Pi.sub_apply] at hAdd hSub
  have hCL := chord_length_integral hK
  have hCH := hit_mass hK
  have hC := (kernel_constants).2.2.2.2 f
  unfold gcIntegral at hCL hCH
  rw [chord_representation hK f]
  unfold gcIntegral
  rw [integral_congr_ae hpoint, hAdd, hSub, integral_const_mul, integral_const_mul]
  unfold Rf gcIntegral
  rw [hC.1, hC.2]
  linear_combination (alphaK f) * hCL - (bK f) * hCH
