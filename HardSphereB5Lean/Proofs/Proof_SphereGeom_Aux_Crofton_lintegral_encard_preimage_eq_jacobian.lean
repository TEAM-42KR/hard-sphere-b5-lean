import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_exists_injective_partition_regular
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_lintegral_encard_fiber_partition
set_option autoImplicit false
open MeasureTheory

theorem proof_SphereGeom_Aux_Crofton_lintegral_encard_preimage_eq_jacobian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → E) (f' : E → E →L[ℝ] E)
    (s : Set E) (hs : MeasurableSet s) (hm : Measurable f')
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    (∫⁻ y, ({x : E | x ∈ s ∧ f x = y}.encard : ENNReal) ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  classical
  let reg : Set E := {x | x ∈ s ∧ (f' x).det ≠ 0}
  let crit : Set E := {x | x ∈ s ∧ (f' x).det = 0}
  have hdet : Measurable (fun x => (f' x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp hm
  have hrm : MeasurableSet reg := hs.inter (hdet (measurableSet_singleton 0).compl)
  have hcm : MeasurableSet crit := hs.inter (hdet (measurableSet_singleton 0))
  have hrd : ∀ x ∈ reg, HasFDerivWithinAt f (f' x) reg x :=
    fun x hx => (hf' x hx.1).mono (fun y hy => hy.1)
  have hcd : ∀ x ∈ crit, HasFDerivWithinAt f (f' x) crit x :=
    fun x hx => (hf' x hx.1).mono (fun y hy => hy.1)
  have hcnull : μ (f '' crit) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hcd (fun x hx => hx.2)
  obtain ⟨t, htm, htd, htu, hti, hts⟩ :=
    SphereGeom.Aux.Crofton.exists_injective_partition_regular f f' reg hrm hrd (fun x hx => hx.2)
  have area : (∫⁻ y, ({x : E | x ∈ reg ∧ f x = y}.encard : ENNReal) ∂μ) =
      ∫⁻ x in reg, ENNReal.ofReal |(f' x).det| ∂μ := by
    have htf : ∀ n x, x ∈ t n → HasFDerivWithinAt f (f' x) (t n) x :=
      fun n x hx => (hrd x (hts n hx)).mono (hts n)
    simpa only [htu] using
      SphereGeom.Aux.Crofton.lintegral_encard_fiber_partition μ f f' t htm htd htf hti
  have hfiber : (fun y => ({x : E | x ∈ s ∧ f x = y}.encard : ENNReal)) =ᵐ[μ]
      (fun y => ({x : E | x ∈ reg ∧ f x = y}.encard : ENNReal)) := by
    have havoid : ∀ᵐ y ∂μ, y ∉ f '' crit := by
      rw [ae_iff]
      have he : {y | ¬ y ∉ f '' crit} = f '' crit := by ext y; simp
      rw [he]; exact hcnull
    filter_upwards [havoid] with y hy
    congr 1
    congr 1
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      refine ⟨⟨hx, ?_⟩, hfx⟩
      intro hzero
      exact hy ⟨x, ⟨hx, hzero⟩, hfx⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨hx.1, hfx⟩
  rw [lintegral_congr_ae hfiber, area]
  have hsu : s = reg ∪ crit := by
    ext x
    simp only [reg, crit, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hdisj : Disjoint reg crit := by
    apply Set.disjoint_left.mpr
    intro x hx hxc
    exact hx.2 hxc.2
  have hzero : ∫⁻ x in crit, ENNReal.ofReal |(f' x).det| ∂μ = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem hcm] with x hx
    simp [hx.2]
  conv_rhs => rw [hsu, lintegral_union hcm hdisj, hzero, add_zero]
