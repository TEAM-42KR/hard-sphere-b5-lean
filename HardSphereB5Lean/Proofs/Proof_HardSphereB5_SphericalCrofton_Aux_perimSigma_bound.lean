import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_activeSphereCircle_measure_le
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_frontierSigma_subset_arcs
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_perimSigma_bound (D : Pt) (hD : D ∈ LamC) :
    0 ≤ perim (SigmaD D) ∧ perim (SigmaD D) ≤ 4 * Real.pi := by
  have hA : arcMeasure (arcA D) ≤ ENNReal.ofReal (2 * π) := by
    by_cases h0 : D = 0
    · simp [arcA,h0]
    · have hnorm : ‖D‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hD.1
      refine (measure_mono ?_).trans (SphereGeom.Aux.activeSphereCircle_measure_le D h0 hnorm)
      intro u hu
      simp only [arcA,if_neg h0,Set.mem_setOf_eq] at hu
      exact ⟨hu.1.1,hu.2⟩
  have hB : arcMeasure (arcB D) ≤ ENNReal.ofReal (2 * π) := by
    by_cases he : D = e
    · simp [arcB,he]
    · have hnorm : ‖D - e‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hD.2
      refine (measure_mono ?_).trans (SphereGeom.Aux.activeSphereCircle_measure_le
        (D - e) (sub_ne_zero.mpr he) hnorm)
      intro u hu
      simp only [arcB,if_neg he,Set.mem_setOf_eq] at hu
      refine ⟨hu.1.1, ?_⟩
      simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hu.2
  have hmeasure : arcMeasure (sFrontier (SigmaD D)) ≤ ENNReal.ofReal (4 * π) := by
    calc
      arcMeasure (sFrontier (SigmaD D)) ≤ arcMeasure (arcA D ∪ arcB D) :=
        measure_mono (HardSphereB5.SphericalCrofton.Aux.frontierSigma_subset_arcs D)
      _ ≤ arcMeasure (arcA D) + arcMeasure (arcB D) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * π) + ENNReal.ofReal (2 * π) := add_le_add hA hB
      _ = ENNReal.ofReal (4 * π) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  constructor
  · exact ENNReal.toReal_nonneg
  · have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    simpa [perim,len,ENNReal.toReal_ofReal Real.pi_pos.le] using ht
