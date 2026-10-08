import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_sigma_support
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_sigma_axis_cases
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_activeSphereCircle_measure_le
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_label_geometry (D : Pt) (hD : D ∈ LamC)
    (hK : IsRegularRegionCrofton (SigmaD D)) :
    MeasurableSet (arcA D) ∧ MeasurableSet (arcB D) ∧
      arcMeasure (arcA D ∩ arcB D) = 0 ∧ arcMeasure (arcA D) < ⊤ ∧
      arcMeasure (arcB D) < ⊤ := by
  classical
  letI : NullSingletonClass arcMeasure := by
    change NullSingletonClass (Measure.hausdorffMeasure (1 : ℝ) : Measure Pt)
    exact Measure.nullSingletonClass_hausdorff Pt (by norm_num : (0 : ℝ) < 1)
  have hna : ‖D‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hD.1
  have hnb : ‖D - e‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hD.2
  have hfiniteA : arcMeasure (arcA D) < ⊤ := by
    by_cases h0 : D = 0
    · simp [arcA, h0]
    · refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := 2 * Real.pi))
      refine (measure_mono ?_).trans (SphereGeom.Aux.activeSphereCircle_measure_le D h0 hna)
      intro u hu
      simp only [arcA, if_neg h0, Set.mem_setOf_eq] at hu
      exact ⟨hu.1.1, hu.2⟩
  have hfiniteB : arcMeasure (arcB D) < ⊤ := by
    by_cases he : D = e
    · simp [arcB, he]
    · refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := 2 * Real.pi))
      refine (measure_mono ?_).trans (SphereGeom.Aux.activeSphereCircle_measure_le
        (D - e) (sub_ne_zero.mpr he) hnb)
      intro u hu
      simp only [arcB, if_neg he, Set.mem_setOf_eq] at hu
      exact ⟨hu.1.1, by simpa [dist_eq_norm, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using hu.2⟩
  have hnull : arcMeasure (arcA D ∩ arcB D) = 0 := by
    by_cases h0 : D = 0
    · simp [arcA, h0]
    by_cases he : D = e
    · simp [arcB, he]
    have hsubS : arcA D ∩ arcB D ⊆ SigmaD D := by
      intro u hu
      have h := hu.1
      simp only [arcA, if_neg h0, Set.mem_setOf_eq] at h
      exact h.1
    by_cases hoff : offAxis D
    · rcases lt_trichotomy (Rc ‖D‖ ‖D - e‖) 1 with hr | hr | hr
      · obtain ⟨V, W, _, hverts⟩ := (sigma_support D hD hoff).1 hr |>.2
        have hsub : arcA D ∩ arcB D ⊆ {V, W} := by
          rw [← hverts]
          rintro u ⟨hu, hv⟩
          simp only [arcA, if_neg h0, Set.mem_setOf_eq] at hu
          simp only [arcB, if_neg he, Set.mem_setOf_eq] at hv
          exact ⟨hu.1.1, hu.2, hv.2⟩
        exact measure_mono_null hsub ((Set.toFinite ({V, W} : Set Pt)).measure_zero arcMeasure)
      · obtain ⟨V, hsingle⟩ := (sigma_support D hD hoff).2.1 hr
        apply measure_mono_null (hsubS.trans (by rw [hsingle]))
        exact measure_singleton V
      · have hempty := (sigma_support D hD hoff).2.2 hr
        apply measure_mono_null (hsubS.trans (by rw [hempty]))
        exact measure_empty
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, D = t • e := by
        simpa only [offAxis, not_forall, not_not] using hoff
      have heNorm : ‖e‖ = 1 := by simp [HardSphereB5.Lean.e]
      have habst : |t| ≤ 1 := by
        simpa only [ht, norm_smul, heNorm, mul_one, Real.norm_eq_abs] using hna
      have habst1 : |t - 1| ≤ 1 := by
        have ht1 : D - e = (t - 1) • e := by rw [ht, sub_smul, one_smul]
        simpa only [ht1, norm_smul, heNorm, mul_one, Real.norm_eq_abs] using hnb
      have ht0 : 0 < t := by
        have hn : t ≠ 0 := by intro hz; apply h0; simp [ht, hz]
        have := (abs_le.mp habst1).1
        have : 0 ≤ t := by linarith
        exact lt_of_le_of_ne this (Ne.symm hn)
      have ht1 : t < 1 := by
        have hn : t ≠ 1 := by intro hz; apply he; simp [ht, hz]
        exact lt_of_le_of_ne (abs_le.mp habst).2 hn
      have hempty : SigmaD D = ∅ := by
        rw [ht]
        exact sigma_axis_cases.1 t ht0 ht1
      apply measure_mono_null (hsubS.trans (by rw [hempty]))
      exact measure_empty
  have hm := pair_measurable D
  exact ⟨hm.2.1, hm.2.2.1, hnull, hfiniteA, hfiniteB⟩
