import Mathlib
set_option autoImplicit false
open MeasureTheory Asymptotics Filter
open scoped Topology
noncomputable section

private lemma inv_norm_locally : LocallyIntegrable (fun z : ℝ × ℝ => ‖z‖⁻¹) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by simp)
  · filter_upwards [] with z
    simp [Real.rpow_neg_one, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
  · exact (by fun_prop : Measurable (fun z : ℝ × ℝ => ‖z‖⁻¹)).aestronglyMeasurable

private lemma inv_norm_shift_locally (p : ℝ × ℝ) :
    LocallyIntegrable (fun z : ℝ × ℝ => ‖z - p‖⁻¹) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let e := Homeomorph.subRight p
  have hm : MeasurePreserving e (volume : Measure (ℝ × ℝ)) volume := by
    exact measurePreserving_sub_right volume p
  have hbase := inv_norm_locally.integrableOn_isCompact (hK.image e.continuous)
  have hcomp := (hm.integrableOn_comp_preimage e.measurableEmbedding).mpr hbase
  rw [e.injective.preimage_image] at hcomp
  exact hcomp

theorem proof_SphereGeom_Aux_Santalo_compact_inverse_integrable (S : (ℝ × ℝ) → ℝ) (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hS : Continuous S) (hnonneg : ∀ z ∈ K, 0 ≤ S z)
    (hlocal : ∀ p ∈ K, S p = 0 → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ z in 𝓝[K] p, c * ‖z - p‖ ≤ S z) :
    IntegrableOn (fun z => (S z)⁻¹) K volume := by
  have hmeas : StronglyMeasurable (fun z => (S z)⁻¹) := hS.measurable.inv.stronglyMeasurable
  apply LocallyIntegrableOn.integrableOn_isCompact _ hK
  intro p hp
  haveI : (𝓝[K] p).IsMeasurablyGenerated := hK.measurableSet.nhdsWithin_isMeasurablyGenerated p
  by_cases hzero : S p = 0
  · obtain ⟨c, hc, hevent⟩ := hlocal p hp hzero
    have hdom : (fun z => (S z)⁻¹) =O[𝓝[K] p] (fun z => ‖z - p‖⁻¹) := by
      apply isBigO_iff.mpr
      refine ⟨c⁻¹, ?_⟩
      filter_upwards [hevent, self_mem_nhdsWithin] with z hz hzK
      by_cases hzp : z = p
      · simp [hzp, hzero]
      · have hdist : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
        have hpos : 0 < S z := lt_of_lt_of_le (mul_pos hc hdist) hz
        simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        calc
          _ ≤ (c * ‖z - p‖)⁻¹ := inv_anti₀ (mul_pos hc hdist) hz
          _ = _ := by rw [mul_inv_rev, mul_comm]
    exact hdom.integrableAtFilter
      ⟨Set.univ, Filter.univ_mem, hmeas.aestronglyMeasurable.restrict⟩
      ((inv_norm_shift_locally p p).filter_mono nhdsWithin_le_nhds)
  · have hcont : ContinuousAt (fun z => (S z)⁻¹) p := hS.continuousAt.inv₀ hzero
    have hb : ∀ᶠ z in 𝓝[K] p, ‖(S z)⁻¹‖ ≤ ‖(S p)⁻¹‖ + 1 :=
      (hcont.norm.eventually (ge_mem_nhds (by linarith : ‖(S p)⁻¹‖ < ‖(S p)⁻¹‖ + 1))).filter_mono nhdsWithin_le_nhds
    have hdom : (fun z => (S z)⁻¹) =O[𝓝[K] p] (fun _ => (1 : ℝ)) := by
      apply isBigO_iff.mpr
      exact ⟨‖(S p)⁻¹‖ + 1, by simpa using hb⟩
    exact hdom.integrableAtFilter
      ⟨Set.univ, Filter.univ_mem, hmeas.aestronglyMeasurable.restrict⟩
      (((continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).locallyIntegrable p).filter_mono nhdsWithin_le_nhds)
