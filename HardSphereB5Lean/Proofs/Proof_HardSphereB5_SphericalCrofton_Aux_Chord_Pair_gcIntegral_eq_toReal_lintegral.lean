import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_kernel_continuous
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_kernel_nonneg
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_gcIntegral_eq_toReal_lintegral {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern) : gcIntegral (fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) = ((1 / 2 : ENNReal) * ∫⁻ p, ENNReal.ofReal ((fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) (greatCircle p)) ∂dOmega).toReal := by
  have hL : Measurable (fun p : Pt => chordLen K (greatCircle p)) :=
    (SphereGeom.Aux.Chord.measurable_arcMeasure_greatCircle_inter K
      hK.isCompact.measurableSet).ennreal_toReal
  have hk : Measurable (fun p : Pt => kK f (chordLen K (greatCircle p))) :=
    (HardSphereB5.SphericalCrofton.Aux.Chord.Interval.kernel_continuous f).measurable.comp hL
  have hm : Measurable (fun p : Pt => if 0 < chordLen K (greatCircle p)
      then kK f (chordLen K (greatCircle p)) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const hL) hk measurable_const
  have hn : ∀ p : Pt, 0 ≤ (if 0 < chordLen K (greatCircle p)
      then kK f (chordLen K (greatCircle p)) else 0) := by
    intro p
    split_ifs
    · exact HardSphereB5.SphericalCrofton.Aux.Chord.Interval.kernel_nonneg f _ ENNReal.toReal_nonneg
    · exact le_refl _
  have hh := integral_eq_lintegral_of_nonneg_ae (μ := dOmega)
    (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable
  unfold gcIntegral
  rw [hh, ENNReal.toReal_mul]
  norm_num [ENNReal.toReal_div]
