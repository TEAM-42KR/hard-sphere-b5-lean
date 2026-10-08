import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_lintegral_arcMeasure_greatCircle
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Chord_arcMeasure_greatCircle_inter_le
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_chord_length_integral {K : Set Pt} (hK : IsRegularRegionCrofton K) :
    gcIntegral (fun G => if 0 < chordLen K G then chordLen K G else 0) = π * sArea K := by
  have hm : Measurable (fun p : Pt => arcMeasure (greatCircle p ∩ K)) :=
    SphereGeom.Aux.Chord.measurable_arcMeasure_greatCircle_inter K hK.isCompact.measurableSet
  have hs : ∀ᵐ p ∂dOmega, ‖p‖ = 1 := by
    have hh : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0 : Pt) 1 :=
      ae_iff.mpr SphereGeom.dOmega_compl_sphere
    filter_upwards [hh] with p hp
    simpa [Metric.mem_sphere, dist_eq_norm] using hp
  have hfinite : ∀ᵐ p ∂dOmega, arcMeasure (greatCircle p ∩ K) < ⊤ := by
    filter_upwards [hs] with p hp
    exact lt_of_le_of_lt (SphereGeom.Aux.Chord.arcMeasure_greatCircle_inter_le p hp K) ENNReal.ofReal_lt_top
  have hin := integral_toReal hm.aemeasurable hfinite
  have hlin := SphereGeom.lintegral_arcMeasure_greatCircle K hK.isCompact.measurableSet hK.subset_sphere
  unfold gcIntegral
  have hif : (fun p : Pt => if 0 < chordLen K (greatCircle p) then chordLen K (greatCircle p) else 0) =
      (fun p : Pt => (arcMeasure (greatCircle p ∩ K)).toReal) := by
    funext p
    unfold chordLen len
    split_ifs with hh
    · rfl
    · exact (le_antisymm (le_of_not_gt hh) ENNReal.toReal_nonneg).symm
  rw [hif, hin, hlin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  unfold sArea
  ring
