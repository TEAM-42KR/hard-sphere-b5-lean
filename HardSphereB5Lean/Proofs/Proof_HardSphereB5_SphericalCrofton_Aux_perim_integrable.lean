import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_perimSigma_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_frontierSigma_subset_arcs
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_frontier_slice
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_sigma_support
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_len_arcA_aestronglyMeasurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_len_arcB_aestronglyMeasurable
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_activeSphereCircle_measure_le
set_option autoImplicit false

open MeasureTheory Set Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
set_option maxHeartbeats 1200000

theorem proof_HardSphereB5_SphericalCrofton_Aux_perim_integrable : IntegrableOn (fun D : Pt => perim (SigmaD D)) LamC := by
  letI : NullSingletonClass arcMeasure := by
    change NullSingletonClass (Measure.hausdorffMeasure (1 : ℝ) : Measure Pt)
    exact Measure.nullSingletonClass_hausdorff Pt (by norm_num : (0 : ℝ) < 1)
  have hLam : MeasurableSet LamC :=
    (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).measurableSet
  have hpoint (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) :
      perim (SigmaD D) = len (arcA D) + len (arcB D) := by
    have h0 : D ≠ 0 := by simpa using hoff 0
    have he : D ≠ e := by simpa using hoff 1
    have ha : 0 < ‖D‖ := norm_pos_iff.mpr h0
    have hb : 0 < ‖D - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    have hna : ‖D‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hD.1
    have hnb : ‖D - e‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hD.2
    obtain ⟨hnA, hnB, hcaps⟩ := Aux.Cap.sigma_caps_data D h0 he
    have hsubA : SigmaD D ⊆ cap (nAv D) (‖D‖ / 2) := by
      rw [hcaps]
      exact inter_subset_left
    have hsubB : SigmaD D ⊆ cap (nBv D) (‖D - e‖ / 2) := by
      rw [hcaps]
      exact inter_subset_right
    have hboundary (K : Set Pt) (hsub : SigmaD D ⊆ K) {u : Pt}
        (hu : u ∈ SigmaD D) (hf : u ∈ sFrontier K) : u ∈ sFrontier (SigmaD D) := by
      rcases hf with ⟨y, hy, rfl⟩
      have hys : y ∈ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' SigmaD D := hu
      refine ⟨y, (mem_frontier_iff_notMem_interior hys).2 ?_, rfl⟩
      intro hi
      exact hy.2 (interior_mono (preimage_mono hsub) hi)
    have hface (d u : Pt) (hd : d ≠ 0) (hu : ‖u‖ = 1) (hdu : ‖d + u‖ = 1) :
        inner ℝ ((‖d‖)⁻¹ • (-d)) u = ‖d‖ / 2 := by
      have hs := norm_add_sq_real d u
      rw [hu, hdu] at hs
      have hi : inner ℝ d u = -‖d‖^2 / 2 := by nlinarith
      rw [real_inner_smul_left, inner_neg_left, hi]
      field_simp [norm_ne_zero_iff.mpr hd]
    have hfront : sFrontier (SigmaD D) = arcA D ∪ arcB D := by
      apply Subset.antisymm (Aux.frontierSigma_subset_arcs D)
      rintro u (hu | hu)
      · simp only [arcA, if_neg h0, mem_setOf_eq] at hu
        apply hboundary _ hsubA hu.1
        rw [Aux.Cap.frontier_slice (nAv D) hnA (‖D‖ / 2)
          (by linarith) (by linarith)]
        exact ⟨hu.1.1, hface D u h0 hu.1.1 hu.2⟩
      · simp only [arcB, if_neg he, mem_setOf_eq] at hu
        apply hboundary _ hsubB hu.1
        rw [Aux.Cap.frontier_slice (nBv D) hnB (‖D - e‖ / 2)
          (by linarith) (by linarith)]
        refine ⟨hu.1.1, ?_⟩
        have hdu : ‖(D - e) + u‖ = 1 := by
          simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hu.2
        simpa only [nBv, show e - D = -(D - e) by abel] using
          hface (D - e) u (sub_ne_zero.mpr he) hu.1.1 hdu
    have hA : MeasurableSet (arcA D) := by
      simp only [arcA, if_neg h0]
      have hS : IsClosed (SigmaD D) := by
        unfold SigmaD LamC
        exact (isClosed_eq continuous_norm continuous_const).inter
          ((Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).preimage
            (continuous_const.add continuous_id))
      exact (hS.inter (isClosed_eq (by fun_prop) continuous_const)).measurableSet
    have hB : MeasurableSet (arcB D) := by
      simp only [arcB, if_neg he]
      have hS : IsClosed (SigmaD D) := by
        unfold SigmaD LamC
        exact (isClosed_eq continuous_norm continuous_const).inter
          ((Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).preimage
            (continuous_const.add continuous_id))
      exact (hS.inter (isClosed_eq (by fun_prop) continuous_const)).measurableSet
    have hfiniteA : arcMeasure (arcA D) ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      refine (measure_mono ?_).trans (SphereGeom.Aux.activeSphereCircle_measure_le D h0 hna)
      intro u hu
      simp only [arcA, if_neg h0, mem_setOf_eq] at hu
      exact ⟨hu.1.1, hu.2⟩
    have hfiniteB : arcMeasure (arcB D) ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      refine (measure_mono ?_).trans (SphereGeom.Aux.activeSphereCircle_measure_le
        (D - e) (sub_ne_zero.mpr he) hnb)
      intro u hu
      simp only [arcB, if_neg he, mem_setOf_eq] at hu
      exact ⟨hu.1.1, by simpa [dist_eq_norm, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using hu.2⟩
    have hsubS : arcA D ∩ arcB D ⊆ SigmaD D := by
      intro u hu
      have h := hu.1
      simp only [arcA, if_neg h0, mem_setOf_eq] at h
      exact h.1
    have hnull : arcMeasure (arcA D ∩ arcB D) = 0 := by
      rcases lt_trichotomy (Rc ‖D‖ ‖D - e‖) 1 with hr | hr | hr
      · obtain ⟨V, W, _, hverts⟩ := (sigma_support D hD hoff).1 hr |>.2
        have hsub : arcA D ∩ arcB D ⊆ {V, W} := by
          rw [← hverts]
          rintro u ⟨hu, hv⟩
          simp only [arcA, if_neg h0, mem_setOf_eq] at hu
          simp only [arcB, if_neg he, mem_setOf_eq] at hv
          exact ⟨hu.1.1, hu.2, hv.2⟩
        exact measure_mono_null hsub ((Set.toFinite ({V, W} : Set Pt)).measure_zero arcMeasure)
      · obtain ⟨V, hsingle⟩ := (sigma_support D hD hoff).2.1 hr
        apply measure_mono_null (hsubS.trans (by rw [hsingle]))
        exact measure_singleton V
      · have hempty := (sigma_support D hD hoff).2.2 hr
        apply measure_mono_null (hsubS.trans (by rw [hempty]))
        exact measure_empty
    have hsum := measure_union_add_inter (μ := arcMeasure) (arcA D) hB
    rw [hnull, add_zero] at hsum
    simp only [perim, len, hfront, hsum, ENNReal.toReal_add hfiniteA hfiniteB]
  let L : Submodule ℝ Pt := Submodule.span ℝ ({e} : Set Pt)
  have hproper : L ≠ ⊤ := by
    intro htop
    have he1 : e1 ∈ L := by rw [htop]; exact Submodule.mem_top
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he1
    have hc := congrArg (fun p : Pt => p (1 : Fin 3)) ht
    simpa [e, e1] using hc
  have haxis : volume {D : Pt | ¬ offAxis D} = 0 := by
    apply measure_mono_null _ (Measure.addHaar_submodule (volume : Measure Pt) L hproper)
    intro D hD
    obtain ⟨t, ht⟩ : ∃ t : ℝ, D = t • e := by simpa only [mem_setOf_eq, offAxis, not_forall, not_not] using hD
    exact Submodule.mem_span_singleton.mpr ⟨t, ht.symm⟩
  have hoff : ∀ᵐ D ∂(volume.restrict LamC), offAxis D :=
    ae_restrict_of_ae (ae_iff.mpr haxis)
  have heq : (fun D : Pt => len (arcA D) + len (arcB D)) =ᵐ[volume.restrict LamC]
      (fun D : Pt => perim (SigmaD D)) := by
    filter_upwards [ae_restrict_mem hLam, hoff] with D hD hOff
    exact (hpoint D hD hOff).symm
  have hm : AEStronglyMeasurable (fun D : Pt => perim (SigmaD D)) (volume.restrict LamC) :=
    (Aux.len_arcA_aestronglyMeasurable.add Aux.len_arcB_aestronglyMeasurable).congr heq
  have hfinite : volume LamC < ⊤ :=
    lt_of_le_of_lt (measure_mono (show LamC ⊆ Metric.closedBall (0 : Pt) 1 from inter_subset_left))
      (measure_closedBall_lt_top (μ := volume) (x := (0 : Pt)) (r := 1))
  refine ⟨hm, HasFiniteIntegral.restrict_of_bounded (4 * Real.pi) hfinite ?_⟩
  filter_upwards [ae_restrict_mem hLam] with D hD
  rw [Real.norm_eq_abs, abs_of_nonneg (Aux.perimSigma_bound D hD).1]
  exact (Aux.perimSigma_bound D hD).2
