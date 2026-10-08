import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_singleton_patch (f : Kern) (D V : Pt) (hK : SigmaD D = {V}) : Rf f (SigmaD D) = AAf f D + BBf f D + ABf f D := by
  have hm : arcMeasure ({V} : Set Pt) = 0 := by
    unfold arcMeasure
    letI := Measure.nullSingletonClass_hausdorff Pt (by norm_num : 0 < (1 : ℝ))
    exact measure_singleton V
  have hzero (S : Set Pt) (hS : S ⊆ {V}) : arcMeasure S = 0 := measure_mono_null hS hm
  have ha : arcA D ⊆ {V} := by
    intro u hu
    unfold arcA at hu
    split_ifs at hu with hd
    · simp at hu
    · simpa [hK] using hu.1
  have hb : arcB D ⊆ {V} := by
    intro u hu
    unfold arcB at hu
    split_ifs at hu with hd
    · simp at hu
    · simpa [hK] using hu.1
  have hra : arcMeasure.restrict (arcA D) = 0 := Measure.restrict_eq_zero.mpr (hzero _ ha)
  have hrb : arcMeasure.restrict (arcB D) = 0 := Measure.restrict_eq_zero.mpr (hzero _ hb)
  have hcg (G : Set Pt) : chordLen (SigmaD D) G = 0 := by
    rw [hK]
    unfold chordLen len
    rw [hzero _ Set.inter_subset_right]
    simp
  simp [AAf, BBf, ABf, hra, hrb, Rf, hcg, gcIntegral]
