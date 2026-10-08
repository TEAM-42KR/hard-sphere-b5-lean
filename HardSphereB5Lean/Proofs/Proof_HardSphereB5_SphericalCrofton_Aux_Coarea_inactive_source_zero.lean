import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_sigma_axis_cases
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_sigma_subsingleton
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_inactive_source_zero (D : Pt) (hD : D ∈ LamC)
    (h : ¬ (offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1)) (F : Pt → Pt → ℝ) :
    (∫ u in arcA D, ∫ v in arcB D, F u v ∂arcMeasure ∂arcMeasure) = 0 := by
  by_cases hz : D = 0
  · subst D
    simp [arcA]
  by_cases he : D = e
  · subst D
    simp [arcB]
  by_cases hoff : offAxis D
  · have hr : 1 ≤ Rc ‖D‖ ‖D - e‖ :=
      le_of_not_gt (fun hr => h ⟨hoff, hr⟩)
    have hs := HardSphereB5.SphericalCrofton.Aux.Santalo.inactive_sigma_subsingleton D hD hoff hr
    have hsub : arcA D ⊆ SigmaD D := by
      intro u hu
      simp only [arcA, if_neg hz, Set.mem_setOf_eq] at hu
      exact hu.1
    letI : NullSingletonClass (arcMeasure : Measure Pt) :=
      Measure.nullSingletonClass_hausdorff Pt (by norm_num : (0 : ℝ) < 1)
    have hnull : arcMeasure (arcA D) = 0 := (hs.anti hsub).measure_zero arcMeasure
    have hrestr : arcMeasure.restrict (arcA D) = 0 := Measure.restrict_eq_zero.mpr hnull
    simp [hrestr]
  · have haxis : ∃ t : ℝ, D = t • e := by
      simpa only [offAxis, not_forall, not_not] using hoff
    obtain ⟨t, rfl⟩ := haxis
    have hnorme : ‖e‖ = 1 := by simp [HardSphereB5.Lean.e]
    have hbounds : ‖t • e‖ ≤ 1 ∧ ‖t • e - e‖ ≤ 1 := by
      simpa only [LamC, Set.mem_inter_iff, Metric.mem_closedBall,
        dist_zero_right, dist_eq_norm, sub_zero] using hD
    have hta : |t| ≤ 1 := by
      simpa only [norm_smul, hnorme, mul_one, Real.norm_eq_abs] using hbounds.1
    have htb : |t - 1| ≤ 1 := by
      have hv : t • e - e = (t - 1) • e := by rw [sub_smul, one_smul]
      rw [hv] at hbounds
      simpa only [norm_smul, hnorme, mul_one, Real.norm_eq_abs] using hbounds.2
    have ht0 : 0 < t := by
      have hn : 0 ≤ t := by linarith [(abs_le.mp htb).1]
      have hne : t ≠ 0 := by
        intro ht
        apply hz
        simp [ht]
      exact lt_of_le_of_ne hn (Ne.symm hne)
    have ht1 : t < 1 := by
      have hn : t ≤ 1 := (abs_le.mp hta).2
      have hne : t ≠ 1 := by
        intro ht
        apply he
        simp [ht]
      exact lt_of_le_of_ne hn hne
    have hSigma : SigmaD (t • e) = ∅ := HardSphereB5.SphericalCrofton.sigma_axis_cases.1 t ht0 ht1
    have hArc : arcA (t • e) = ∅ := by simp [arcA, hz, hSigma]
    simp [hArc]
