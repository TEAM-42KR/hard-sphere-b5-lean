import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Chord_arcMeasure_greatCircle_inter_le (p : E3) (hp : ‖p‖ = 1) (A : Set E3) :
    arcMeasure (greatCircle p ∩ A) ≤ ENNReal.ofReal (2 * Real.pi) := by
  obtain ⟨F₁, F₂, -, -, hF⟩ := SphereGeom.exists_measurable_frame
  have h := SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame (F₁ p) (F₂ p) p (hF p hp)
  have hcont : Continuous fun t : ℝ => circlePt 0 (F₁ p) (F₂ p) 1 t := by
    unfold circlePt
    fun_prop
  have hmeas : Measurable (circlePt 0 (F₁ p) (F₂ p) 1) := hcont.measurable
  calc arcMeasure (greatCircle p ∩ A) ≤ arcMeasure (greatCircle p) :=
        measure_mono Set.inter_subset_left
    _ = arcMeasure.restrict (greatCircle p) Set.univ := by
        rw [Measure.restrict_apply_univ]
    _ = (volume.restrict (Set.Icc (-Real.pi) Real.pi)) Set.univ := by
        rw [h, Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ]
    _ = ENNReal.ofReal (2 * Real.pi) := by
        rw [Measure.restrict_apply_univ, Real.volume_Icc]
        congr 1
        ring
