import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem dOmega_singleton_zero (x : Pt) : dOmega {x} = 0 := by
  have he : ‖(e : Pt)‖ = 1 := by simp [HardSphereB5.Lean.e, EuclideanSpace.norm_eq]
  have hh : dOmega ((fun u : Pt => inner ℝ e u) ⁻¹' {inner ℝ e x}) = 0 := by
    rw [← Measure.map_apply (by fun_prop : Measurable (fun u : Pt => inner ℝ e u)) (measurableSet_singleton _), SphereGeom.dOmega_map_inner e he]
    simp only [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton _)]
    have hm : (volume : Measure ℝ) ({inner ℝ e x} ∩ Set.Icc (-1) 1) = 0 :=
      measure_mono_null Set.inter_subset_left (measure_singleton _)
    rw [hm, smul_zero]
  exact measure_mono_null (by intro u hu; rw [Set.mem_singleton_iff] at hu; subst u; exact Set.mem_singleton _) hh

private theorem arc_singleton_zero (x : Pt) : arcMeasure {x} = 0 := by
  letI := Measure.nullSingletonClass_hausdorff Pt (by norm_num : (0 : ℝ) < 1)
  change (Measure.hausdorffMeasure 1 : Measure Pt) {x} = 0
  exact measure_singleton x

private theorem singleton_small_values (x : Pt) (f : Kern) :
    Ff f {x} = 0 ∧ sArea {x} = 0 ∧ perim {x} = 0 ∧ Rf f {x} = 0 := by
  have hd := dOmega_singleton_zero x
  have ha := arc_singleton_zero x
  have hfr : sFrontier ({x} : Set Pt) ⊆ ({x} : Set Pt) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact (isClosed_singleton.preimage continuous_subtype_val).frontier_subset hw
  have hlen : ∀ G : Set Pt, chordLen {x} G = 0 := by
    intro G
    have hz : arcMeasure (G ∩ {x}) = 0 := measure_mono_null Set.inter_subset_right ha
    simp only [chordLen, len, hz, ENNReal.toReal_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Ff
    rw [Measure.restrict_eq_zero.mpr hd]
    simp
  · simp only [sArea, hd, ENNReal.toReal_zero]
  · have hzero := measure_mono_null hfr ha
    simp only [perim, len, hzero, ENNReal.toReal_zero]
  · unfold Rf
    simp only [hlen, lt_self_iff_false, false_and, if_false]
    simp [gcIntegral]

theorem proof_HardSphereB5_SphericalCrofton_Aux_small_region_zero (K : Set Pt) (hK : K.Subsingleton) (f : Kern) :
    Ff f K = 0 ∧ sArea K = 0 ∧ perim K = 0 ∧ Rf f K = 0 := by
  rcases hK.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · simp [Ff, sArea, perim, len, sFrontier, Rf, chordLen, gcIntegral]
  · exact singleton_small_values x f
