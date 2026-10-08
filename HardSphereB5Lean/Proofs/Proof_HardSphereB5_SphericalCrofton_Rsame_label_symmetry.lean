import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_phiK_nonneg
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_AAf_aestronglyMeasurable
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem LamC_reflection_iff (x : Pt) : e - x ∈ LamC ↔ x ∈ LamC := by
  have h0 : dist (e - x) 0 = dist x e := by
    simp only [dist_eq_norm, sub_zero, norm_sub_rev]
  have he : dist (e - x) e = dist x 0 := by
    rw [dist_eq_norm, dist_eq_norm, sub_zero, show e - x - e = -x by abel, norm_neg]
  simp only [LamC, Set.mem_inter_iff, Metric.mem_closedBall, h0, he]
  exact and_comm

private theorem SigmaD_neg_mem_iff (D u : Pt) : -u ∈ SigmaD (e - D) ↔ u ∈ SigmaD D := by
  simp only [SigmaD, Set.mem_setOf_eq, norm_neg]
  rw [show e - D + -u = e - (D + u) by abel, LamC_reflection_iff]

private theorem SigmaD_reflection (D : Pt) : SigmaD (e - D) = Neg.neg '' SigmaD D := by
  ext u
  constructor
  · intro hu
    refine ⟨-u, (SigmaD_neg_mem_iff D (-u)).mp ?_, by simp⟩
    simpa only [neg_neg] using hu
  · rintro ⟨v, hv, rfl⟩
    exact (SigmaD_neg_mem_iff D v).mpr hv

private theorem norm_reflected_contact (D u : Pt) : ‖e - D + -u‖ = dist (D + u) e := by
  rw [show e - D + -u = e - (D + u) by abel, norm_sub_rev, dist_eq_norm]

private theorem arcA_neg_mem_iff (D u : Pt) : -u ∈ arcA (e - D) ↔ u ∈ arcB D := by
  by_cases hD : D = e
  · simp [arcA, arcB, hD]
  · have h0 : e - D ≠ 0 := by
      intro h
      exact hD ((sub_eq_zero.mp h).symm)
    simp only [arcA, arcB, if_neg h0, if_neg hD, Set.mem_setOf_eq,
      SigmaD_neg_mem_iff, norm_reflected_contact]

private theorem arcA_reflection_preimage (D : Pt) : Neg.neg ⁻¹' arcA (e - D) = arcB D := by
  ext u
  exact arcA_neg_mem_iff D u

private theorem nAv_reflection (D : Pt) : nAv (e - D) = -nBv D := by
  simp only [nAv, nBv, norm_sub_rev e D, ← smul_neg]

private theorem cross_neg_neg (u v : Pt) : cross (-u) (-v) = cross u v := by
  simp [SphereGeom.cross, map_neg]

private theorem tanA_reflection (D u : Pt) : tanA (e - D) (-u) = tanB D u := by
  rw [tanA, tanB, nAv_reflection, cross_neg_neg]

private theorem santaloDens_neg_neg (u v τ1 τ2 : Pt) :
    santaloDens (-u) (-v) τ1 τ2 = santaloDens u v τ1 τ2 := by
  simp only [santaloDens, cross_neg_neg, inner_neg_neg]

private theorem santaloDens_reflection (D u v : Pt) :
    santaloDens (-u) (-v) (tanA (e - D) (-u)) (tanA (e - D) (-v)) =
      santaloDens u v (tanB D u) (tanB D v) := by
  rw [tanA_reflection, tanA_reflection, santaloDens_neg_neg]

private theorem neg_arc_measure_preserving : MeasurePreserving (Neg.neg : Pt → Pt) arcMeasure arcMeasure := by
  exact (IsometryEquiv.neg Pt).measurePreserving_hausdorffMeasure 1

private theorem neg_embedding : MeasurableEmbedding (Neg.neg : Pt → Pt) := by
  simpa using (Homeomorph.neg Pt).measurableEmbedding

private theorem AAf_reflection_of_geometry (f : Kern)
    (hArc : ∀ D, (Neg.neg : Pt → Pt) ⁻¹' arcA (e - D) = arcB D)
    (hDens : ∀ D u v, santaloDens (-u) (-v) (tanA (e - D) (-u)) (tanA (e - D) (-v)) =
      santaloDens u v (tanB D u) (tanB D v)) (D : Pt) :
    AAf f (e - D) = BBf f D := by
  unfold AAf BBf
  congr 1
  rw [← neg_arc_measure_preserving.setIntegral_preimage_emb neg_embedding _ (arcA (e - D)), hArc]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← neg_arc_measure_preserving.setIntegral_preimage_emb neg_embedding _ (arcA (e - D)), hArc]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [inner_neg_neg, hDens]

private theorem reflection_preimage_LamC : (fun D : Pt => e - D) ⁻¹' LamC = LamC := by
  ext D
  simp only [LamC, Set.mem_preimage, Set.mem_inter_iff, Metric.mem_closedBall,
    dist_zero_right, dist_eq_norm, sub_zero]
  have h1 : ‖e - D‖ = ‖D - e‖ := norm_sub_rev e D
  have h2 : ‖e - D - e‖ = ‖D‖ := by rw [show e - D - e = -D by abel, norm_neg]
  rw [h1, h2]
  exact and_comm

private theorem reflection_measure_preserving : MeasurePreserving (fun D : Pt => e - D) volume volume := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_left (volume : Measure Pt) e).comp (Measure.measurePreserving_neg (volume : Measure Pt))

private theorem reflection_embedding : MeasurableEmbedding (fun D : Pt => e - D) := by
  simpa [Function.comp_def, sub_eq_add_neg] using
    (Homeomorph.addLeft e).measurableEmbedding.comp (Homeomorph.neg Pt).measurableEmbedding

private theorem Rsame_label_symmetry_of_integrable (f : Kern)
    (hA : IntegrableOn (AAf f) LamC) :
    Rsame f = 2 * ∫ D in LamC, AAf f D := by
  have hlabel : ∀ D, AAf f (e - D) = BBf f D :=
    fun D => AAf_reflection_of_geometry f arcA_reflection_preimage santaloDens_reflection D
  have hB : IntegrableOn (BBf f) LamC := by
    have hh := (reflection_measure_preserving.integrableOn_comp_preimage reflection_embedding).mpr hA
    rw [reflection_preimage_LamC] at hh
    convert hh using 1
    exact (funext hlabel).symm
  have hint : (∫ D in LamC, BBf f D) = ∫ D in LamC, AAf f D := by
    have hh := reflection_measure_preserving.setIntegral_preimage_emb reflection_embedding (AAf f) LamC
    rw [reflection_preimage_LamC] at hh
    simpa only [hlabel] using hh
  unfold Rsame
  rw [integral_add hA hB, hint]
  ring

private theorem cutKern_nonneg (f : Kern) (δ : ℝ) (hδ : 0 ≤ δ) : 0 ≤ cutKern f δ := by
  unfold cutKern
  split_ifs with h
  · exact phiK_nonneg f δ hδ (le_of_lt h)
  · rfl

private theorem santaloDens_nonneg (u v τ1 τ2 : Pt) : 0 ≤ santaloDens u v τ1 τ2 := by
  unfold santaloDens
  apply div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact pow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩) 3

private theorem AAf_nonneg (f : Kern) (D : Pt) : 0 ≤ AAf f D := by
  unfold AAf
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro u
  apply integral_nonneg
  intro v
  exact mul_nonneg (cutKern_nonneg f _ (Real.arccos_nonneg _)) (santaloDens_nonneg _ _ _ _)

private theorem BBf_nonneg (f : Kern) (D : Pt) : 0 ≤ BBf f D := by
  unfold BBf
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro u
  apply integral_nonneg
  intro v
  exact mul_nonneg (cutKern_nonneg f _ (Real.arccos_nonneg _)) (santaloDens_nonneg _ _ _ _)

theorem proof_HardSphereB5_SphericalCrofton_Rsame_label_symmetry (f : Kern) :
    Rsame f = 2 * ∫ D in LamC, AAf f D := by
  have hMeas := HardSphereB5.SphericalCrofton.Aux.AAf_aestronglyMeasurable f
  by_cases hA : IntegrableOn (AAf f) LamC
  · exact Rsame_label_symmetry_of_integrable f hA
  · have hSum : ¬ Integrable (fun D => AAf f D + BBf f D) (volume.restrict LamC) := by
      intro hSum
      apply hA
      apply hSum.mono' hMeas
      exact Filter.Eventually.of_forall (fun D => by
        rw [Real.norm_eq_abs, abs_of_nonneg (AAf_nonneg f D)]
        linarith [BBf_nonneg f D])
    unfold Rsame
    rw [integral_undef hSum, integral_undef hA]
    ring
