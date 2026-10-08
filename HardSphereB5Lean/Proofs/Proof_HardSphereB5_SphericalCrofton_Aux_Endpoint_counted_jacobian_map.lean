import Mathlib
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_lintegral_encard_preimage_eq_jacobian
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_counted_jacobian_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (f' : E → E →L[ℝ] E) (s H : Set E)
    (hf : Measurable f) (hs : MeasurableSet s) (hH : MeasurableSet H)
    (hm : Measurable f')
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcount : ∀ᵐ y ∂μ, ({x : E | x ∈ s ∧ f x = y}.encard : ENNReal) =
      H.indicator (fun _ => (1 : ENNReal)) y) :
    ((μ.restrict s).withDensity (fun x => ENNReal.ofReal |(f' x).det|)).map f =
      μ.restrict H := by
  classical
  apply Measure.ext
  intro T hT
  have hpre : MeasurableSet (f ⁻¹' T) := hT.preimage hf
  have hcut : MeasurableSet (s ∩ f ⁻¹' T) := hs.inter hpre
  have hderiv : ∀ x ∈ s ∩ f ⁻¹' T,
      HasFDerivWithinAt f (f' x) (s ∩ f ⁻¹' T) x :=
    fun x hx => (hf' x hx.1).mono Set.inter_subset_left
  have harea := SphereGeom.Aux.Crofton.lintegral_encard_preimage_eq_jacobian
    μ f f' (s ∩ f ⁻¹' T) hcut hm hderiv
  have hcutcount : (fun y =>
      ({x : E | x ∈ s ∩ f ⁻¹' T ∧ f x = y}.encard : ENNReal)) =ᵐ[μ]
      T.indicator (H.indicator (fun _ => (1 : ENNReal))) := by
    filter_upwards [hcount] with y hyc
    by_cases hy : y ∈ T
    · rw [Set.indicator_of_mem hy]
      have hfiber : {x : E | x ∈ s ∩ f ⁻¹' T ∧ f x = y} =
          {x : E | x ∈ s ∧ f x = y} := by
        ext x
        constructor
        · rintro ⟨⟨hxs, _⟩, hxy⟩
          exact ⟨hxs, hxy⟩
        · rintro ⟨hxs, hxy⟩
          refine ⟨⟨hxs, ?_⟩, hxy⟩
          change f x ∈ T
          rwa [hxy]
      rw [hfiber]
      exact hyc
    · rw [Set.indicator_of_notMem hy]
      have hfiber : {x : E | x ∈ s ∩ f ⁻¹' T ∧ f x = y} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hxt⟩, hxy⟩
        exact hy (hxy ▸ hxt)
      simp only [hfiber, Set.encard_empty, ENat.toENNReal_zero]
  rw [Measure.map_apply hf hT, withDensity_apply _ hpre,
    Measure.restrict_restrict hpre, Set.inter_comm (f ⁻¹' T) s,
    ← harea, lintegral_congr_ae hcutcount,
    lintegral_indicator hT, lintegral_indicator hH,
    lintegral_one, Measure.restrict_restrict hH,
    Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.restrict_apply hT]
  rw [Set.inter_comm]
