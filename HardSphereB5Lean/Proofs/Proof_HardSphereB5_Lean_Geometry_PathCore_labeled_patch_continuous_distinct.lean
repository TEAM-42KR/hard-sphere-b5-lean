import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section

open Set Filter MeasureTheory
open scoped Topology

private abbrev S5b_PatchContinuity_E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S5b_PatchContinuity_Centres := Fin 4 → S5b_PatchContinuity_E3

private def S5b_PatchContinuity_cut (d : S5b_PatchContinuity_Centres) (i : Fin 4) : Set S5b_PatchContinuity_E3 :=
  {u | ∀ j, j ≠ i → dist (d i + u) (d j) ≤ 1}

private theorem S5b_PatchContinuity_cut_isClosed (d : S5b_PatchContinuity_Centres) (i : Fin 4) : IsClosed (S5b_PatchContinuity_cut d i) := by
  have heq : S5b_PatchContinuity_cut d i = ⋂ j : Fin 4, ⋂ (_ : j ≠ i),
      {u : S5b_PatchContinuity_E3 | dist (d i + u) (d j) ≤ (1 : ℝ)} := by
    ext u
    simp only [S5b_PatchContinuity_cut, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) continuous_const

private theorem S5b_PatchContinuity_cut_measurable (d : S5b_PatchContinuity_Centres) (i : Fin 4) : MeasurableSet (S5b_PatchContinuity_cut d i) :=
  (S5b_PatchContinuity_cut_isClosed d i).measurableSet

private theorem S5b_PatchContinuity_cut_membership_eventually (c : S5b_PatchContinuity_Centres) (i : Fin 4) (u : S5b_PatchContinuity_E3)
    (haway : ∀ j, j ≠ i → dist (c i + u) (c j) ≠ 1) :
    ∀ᶠ d in 𝓝 c, (u ∈ S5b_PatchContinuity_cut d i ↔ u ∈ S5b_PatchContinuity_cut c i) := by
  have hpred : ∀ j : Fin 4, ∀ᶠ d : S5b_PatchContinuity_Centres in 𝓝 c,
      j ≠ i → (dist (d i + u) (d j) ≤ 1 ↔ dist (c i + u) (c j) ≤ 1) := by
    intro j
    by_cases hji : j ≠ i
    · have hd : ContinuousAt (fun d : S5b_PatchContinuity_Centres => dist (d i + u) (d j)) c := by
        fun_prop
      rcases lt_or_gt_of_ne (haway j hji) with hlt | hgt
      · filter_upwards [hd.tendsto.eventually_lt_const hlt] with d hd'
        intro _
        exact iff_of_true hd'.le hlt.le
      · filter_upwards [hd.tendsto.eventually_const_lt hgt] with d hd'
        intro _
        exact iff_of_false (not_le.mpr hd') (not_le.mpr hgt)
    · exact Eventually.of_forall fun _ hj => (hji hj).elim
  filter_upwards [Filter.eventually_all.mpr hpred] with d hd
  change (∀ j, j ≠ i → dist (d i + u) (d j) ≤ 1) ↔
    (∀ j, j ≠ i → dist (c i + u) (c j) ≤ 1)
  exact ⟨fun h j hj => (hd j hj).mp (h j hj),
    fun h j hj => (hd j hj).mpr (h j hj)⟩

private theorem S5b_PatchContinuity_indicator_continuousAt {F : Type*} [Zero F] [TopologicalSpace F]
    (c : S5b_PatchContinuity_Centres) (i : Fin 4) (g : S5b_PatchContinuity_E3 → F) (u : S5b_PatchContinuity_E3)
    (haway : ∀ j, j ≠ i → dist (c i + u) (c j) ≠ 1) :
    ContinuousAt (fun d => (S5b_PatchContinuity_cut d i).indicator g u) c := by
  have heq : (fun d => (S5b_PatchContinuity_cut d i).indicator g u) =ᶠ[𝓝 c]
      (fun _ : S5b_PatchContinuity_Centres => (S5b_PatchContinuity_cut c i).indicator g u) := by
    filter_upwards [S5b_PatchContinuity_cut_membership_eventually c i u haway] with d hd
    by_cases huc : u ∈ S5b_PatchContinuity_cut c i
    · rw [Set.indicator_of_mem (hd.mpr huc), Set.indicator_of_mem huc]
    · rw [Set.indicator_of_notMem (fun hud => huc (hd.mp hud)),
        Set.indicator_of_notMem huc]
  exact continuousAt_const.congr heq.symm

private theorem S5b_PatchContinuity_ae_indicator_continuousAt {F : Type*} [Zero F] [TopologicalSpace F]
    (μ : Measure S5b_PatchContinuity_E3) (c : S5b_PatchContinuity_Centres) (i : Fin 4) (g : S5b_PatchContinuity_E3 → F)
    (hbound : ∀ j, j ≠ i → ∀ᵐ u ∂μ, dist (c i + u) (c j) ≠ 1) :
    ∀ᵐ u ∂μ, ContinuousAt (fun d => (S5b_PatchContinuity_cut d i).indicator g u) c := by
  have hall : ∀ᵐ u ∂μ, ∀ j : Fin 4,
      j ≠ i → dist (c i + u) (c j) ≠ 1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j ≠ i
    · filter_upwards [hbound j hji] with u hu
      exact fun _ => hu
    · exact Eventually.of_forall fun _ hj => (hji hj).elim
  filter_upwards [hall] with u hu
  exact S5b_PatchContinuity_indicator_continuousAt c i g u hu

private theorem S5b_PatchContinuity_area_continuousAt (μ : Measure S5b_PatchContinuity_E3) [IsFiniteMeasure μ]
    (c : S5b_PatchContinuity_Centres) (i : Fin 4)
    (hbound : ∀ j, j ≠ i → ∀ᵐ u ∂μ, dist (c i + u) (c j) ≠ 1) :
    ContinuousAt (fun d => ∫ u, (S5b_PatchContinuity_cut d i).indicator (fun _ => (1 : ℝ)) u ∂μ) c := by
  apply MeasureTheory.continuousAt_of_dominated (bound := fun _ : S5b_PatchContinuity_E3 => (1 : ℝ))
  · exact Eventually.of_forall fun d =>
      aestronglyMeasurable_const.indicator (S5b_PatchContinuity_cut_measurable d i)
  · exact Eventually.of_forall fun d => Eventually.of_forall fun u => by
      simpa using (norm_indicator_le_norm_self (s := S5b_PatchContinuity_cut d i)
        (fun _ : S5b_PatchContinuity_E3 => (1 : ℝ)) u)
  · exact integrable_const 1
  · exact S5b_PatchContinuity_ae_indicator_continuousAt μ c i (fun _ => (1 : ℝ)) hbound

private theorem S5b_PatchContinuity_moment_continuousAt (μ : Measure S5b_PatchContinuity_E3) [IsFiniteMeasure μ]
    (c : S5b_PatchContinuity_Centres) (i : Fin 4) (hunit : ∀ᵐ u ∂μ, ‖u‖ = 1)
    (hbound : ∀ j, j ≠ i → ∀ᵐ u ∂μ, dist (c i + u) (c j) ≠ 1) :
    ContinuousAt (fun d => ∫ u, (S5b_PatchContinuity_cut d i).indicator id u ∂μ) c := by
  apply MeasureTheory.continuousAt_of_dominated (bound := fun _ : S5b_PatchContinuity_E3 => (1 : ℝ))
  · exact Eventually.of_forall fun d =>
      (continuous_id.aestronglyMeasurable (μ := μ)).indicator (S5b_PatchContinuity_cut_measurable d i)
  · refine Eventually.of_forall fun d => ?_
    filter_upwards [hunit] with u hu
    simpa only [id_eq, hu] using
      (norm_indicator_le_norm_self (s := S5b_PatchContinuity_cut d i) (id : S5b_PatchContinuity_E3 → S5b_PatchContinuity_E3) u)
  · exact integrable_const 1
  · exact S5b_PatchContinuity_ae_indicator_continuousAt μ c i id hbound

end

open MeasureTheory SphereGeom
open scoped RealInnerProductSpace

noncomputable section

section

private theorem S5b_SphereNull_ae_unit_dist_ne_one (p q : E3) (hpq : p ≠ q) :
    ∀ᵐ u ∂dOmega, ‖u‖ = 1 ∧ dist (p + u) q ≠ 1 := by
  have hd : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  let n : E3 := (‖q - p‖⁻¹ : ℝ) • (q - p)
  have hn : ‖n‖ = 1 := by
    dsimp [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd),
      inv_mul_cancel₀ (ne_of_gt hd)]
  have hinner : ∀ᵐ u ∂dOmega, inner ℝ n u ≠ ‖q - p‖ / 2 := by
    have hm : ∀ᵐ r ∂dOmega.map (fun u : E3 => inner ℝ n u),
        r ≠ ‖q - p‖ / 2 := by
      apply ae_iff.mpr
      rw [dOmega_map_inner n hn]
      simp
    exact ae_of_ae_map (f := fun u : E3 => inner ℝ n u)
      (p := fun r : ℝ => r ≠ ‖q - p‖ / 2) (by fun_prop) hm
  have hsphere : ∀ᵐ u ∂dOmega, ‖u‖ = 1 := by
    simp only [dOmega, SphereGeom.sphereMeasure, zero_add]
    apply (ae_map_iff continuous_subtype_val.measurable.aemeasurable
      (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
    exact Filter.Eventually.of_forall fun u => mem_sphere_zero_iff_norm.mp u.2
  filter_upwards [hsphere, hinner] with u hu hnu
  refine ⟨hu, ?_⟩
  intro hb
  apply hnu
  change inner ℝ ((‖q - p‖⁻¹ : ℝ) • (q - p)) u = ‖q - p‖ / 2
  have hid : p + u - q = u - (q - p) := by abel
  have he : ‖u - (q - p)‖ = 1 := by
    simpa only [dist_eq_norm, hid] using hb
  have hsq := norm_sub_sq_real u (q - p)
  rw [he, hu, real_inner_comm] at hsq
  rw [real_inner_smul_left]
  field_simp [ne_of_gt hd]
  nlinarith [hsq]

end

noncomputable section
open MeasureTheory Real
open scoped Classical

section
open HardSphereB5.Lean (Pt)

private def S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut (d : Fin 4 → Pt) (i : Fin 4) : Set Pt :=
  {u | ∀ j, j ≠ i → dist (d i + u) (d j) ≤ 1}

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sphereMeasure_shift (p : Pt) :
    HardSphereB5.Lean.Geometry.PathCore.sphereMeasure p = SphereGeom.dOmega.map (fun u : Pt => p + u) := by
  simp only [HardSphereB5.Lean.Geometry.PathCore.sphereMeasure, SphereGeom.dOmega, SphereGeom.sphereMeasure, zero_add]
  exact (Measure.map_map
    (g := fun u : Pt => p + u)
    (f := fun u : Metric.sphere (0 : Pt) 1 => (u : Pt))
    (continuous_const.add continuous_id).measurable
    continuous_subtype_val.measurable).symm

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_dOmega_unit : ∀ᵐ u ∂SphereGeom.dOmega, ‖u‖ = 1 := by
  simp only [SphereGeom.dOmega, SphereGeom.sphereMeasure, zero_add]
  apply (ae_map_iff continuous_subtype_val.measurable.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  exact Filter.Eventually.of_forall fun u => mem_sphere_zero_iff_norm.mp u.2

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_body_measurable (d : Fin 4 → Pt) (F : Finset (Fin 4)) :
    MeasurableSet (body d F) := by
  apply IsClosed.measurableSet
  unfold body
  exact isClosed_iInter fun j => isClosed_iInter fun _ => Metric.isClosed_closedBall

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut_measurable (d : Fin 4 → Pt) (i : Fin 4) :
    MeasurableSet (S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i) := by
  have heq : S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i = ⋂ j : Fin 4, ⋂ (_ : j ≠ i),
      {u : Pt | dist (d i + u) (d j) ≤ 1} := by
    ext u
    simp [S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut]
  rw [heq]
  apply IsClosed.measurableSet
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le ((continuous_const.add continuous_id).dist continuous_const) continuous_const

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_body_shift_mem (d : Fin 4 → Pt) (i : Fin 4) (u : Pt) (hu : ‖u‖ = 1) :
    d i + u ∈ body d Finset.univ ↔ u ∈ S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i := by
  simp only [body, Set.mem_iInter, Finset.mem_univ, forall_true_left, Metric.mem_closedBall]
  change (∀ j, dist (d i + u) (d j) ≤ 1) ↔ ∀ j, j ≠ i → dist (d i + u) (d j) ≤ 1
  constructor
  · intro h j _
    exact h j
  · intro h j
    by_cases hji : j = i
    · subst j
      simp [dist_eq_norm, hu]
    · exact h j hji

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_pArea_fixed (d : Fin 4 → Pt) (i : Fin 4) :
    pArea d i Finset.univ = ∫ u, (S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i).indicator (fun _ => (1 : ℝ)) u
      ∂SphereGeom.dOmega := by
  have hfull : (fun u : Pt => d i + u) ⁻¹' body d Finset.univ =ᵐ[SphereGeom.dOmega] S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i := by
    filter_upwards [S5b_HardSphereB5_Lean_Geometry_PathCore_dOmega_unit] with u hu
    exact propext (S5b_HardSphereB5_Lean_Geometry_PathCore_body_shift_mem d i u hu)
  have hm : SphereGeom.dOmega ((fun u : Pt => d i + u) ⁻¹' body d Finset.univ) =
      SphereGeom.dOmega (S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i) := measure_congr hfull
  calc
    pArea d i Finset.univ =
        (SphereGeom.dOmega ((fun u : Pt => d i + u) ⁻¹' body d Finset.univ)).toReal := by
      simp only [pArea, Finset.mem_univ, if_true, S5b_HardSphereB5_Lean_Geometry_PathCore_sphereMeasure_shift]
      rw [Measure.map_apply (f := fun u : Pt => d i + u) (continuous_const.add continuous_id).measurable
        (S5b_HardSphereB5_Lean_Geometry_PathCore_body_measurable d Finset.univ)]
    _ = (SphereGeom.dOmega (S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i)).toReal := congrArg ENNReal.toReal hm
    _ = ∫ u, (S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i).indicator (fun _ => (1 : ℝ)) u ∂SphereGeom.dOmega := by
      symm
      exact integral_indicator_one (S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut_measurable d i)

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_pMoment_fixed (d : Fin 4 → Pt) (i : Fin 4) :
    pMoment d i Finset.univ = ∫ u, (S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i).indicator (fun u => u) u
      ∂SphereGeom.dOmega := by
  simp only [pMoment, Finset.mem_univ, if_true]
  rw [← integral_indicator (S5b_HardSphereB5_Lean_Geometry_PathCore_body_measurable d Finset.univ), S5b_HardSphereB5_Lean_Geometry_PathCore_sphereMeasure_shift]
  rw [integral_map_of_stronglyMeasurable
    (φ := fun u : Pt => d i + u)
    (f := (body d Finset.univ).indicator (fun x : Pt => x - d i))
    (continuous_const.add continuous_id).measurable
    ((continuous_id.sub continuous_const).stronglyMeasurable.indicator
      (S5b_HardSphereB5_Lean_Geometry_PathCore_body_measurable d Finset.univ))]
  apply integral_congr_ae
  filter_upwards [S5b_HardSphereB5_Lean_Geometry_PathCore_dOmega_unit] with u hu
  have hb := S5b_HardSphereB5_Lean_Geometry_PathCore_body_shift_mem d i u hu
  by_cases hc : u ∈ S5b_HardSphereB5_Lean_Geometry_PathCore_fixedCut d i
  · simp [Set.indicator_of_mem, hc, hb.mpr hc]
  · simp [Set.indicator_of_notMem, hc, mt hb.mp hc]

end

section
open HardSphereB5.Lean (Pt)
open MeasureTheory

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_labeled_patch_continuous_distinct_of_deps (c : Fin 4 → Pt) (hinj : Function.Injective c) (i : Fin 4) :
    ContinuousAt (fun c : Fin 4 → Pt => pArea c i Finset.univ) c ∧
    ContinuousAt (fun c : Fin 4 → Pt => pMoment c i Finset.univ) c := by
  letI : IsFiniteMeasure SphereGeom.dOmega := by
    unfold SphereGeom.dOmega SphereGeom.sphereMeasure
    infer_instance
  have hbound : ∀ j, j ≠ i → ∀ᵐ u ∂SphereGeom.dOmega, dist (c i + u) (c j) ≠ 1 := by
    intro j hji
    have hcij : c i ≠ c j := fun he => hji (hinj he).symm
    filter_upwards [S5b_SphereNull_ae_unit_dist_ne_one (c i) (c j) hcij] with u hu
    exact hu.2
  have harea := S5b_PatchContinuity_area_continuousAt SphereGeom.dOmega c i hbound
  have hmoment := S5b_PatchContinuity_moment_continuousAt SphereGeom.dOmega c i S5b_HardSphereB5_Lean_Geometry_PathCore_dOmega_unit hbound
  constructor
  · have heq : (fun d : Fin 4 → Pt => pArea d i Finset.univ) =
        (fun d : Fin 4 → Pt => ∫ u, (S5b_PatchContinuity_cut d i).indicator
          (fun _ => (1 : ℝ)) u ∂SphereGeom.dOmega) := by
      funext d
      exact S5b_HardSphereB5_Lean_Geometry_PathCore_pArea_fixed d i
    rw [heq]
    exact harea
  · have heq : (fun d : Fin 4 → Pt => pMoment d i Finset.univ) =
        (fun d : Fin 4 → Pt => ∫ u, (S5b_PatchContinuity_cut d i).indicator id u ∂SphereGeom.dOmega) := by
      funext d
      exact S5b_HardSphereB5_Lean_Geometry_PathCore_pMoment_fixed d i
    rw [heq]
    exact hmoment

end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_labeled_patch_continuous_distinct (c : Fin 4 → Pt) (hinj : Function.Injective c) (i : Fin 4) :
  ContinuousAt (fun c : Fin 4 → Pt => pArea c i Finset.univ) c ∧
  ContinuousAt (fun c : Fin 4 → Pt => pMoment c i Finset.univ) c := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_labeled_patch_continuous_distinct_of_deps c hinj i

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_labeled_patch_continuous_distinct
