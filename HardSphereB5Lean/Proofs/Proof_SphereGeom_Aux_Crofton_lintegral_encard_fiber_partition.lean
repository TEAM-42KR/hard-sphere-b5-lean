import Mathlib
set_option autoImplicit false
open MeasureTheory

private theorem area_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → E) (f' : E → E →L[ℝ] E)
    (s : ℕ → Set E) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hf' : ∀ n x, x ∈ s n → HasFDerivWithinAt f (f' x) (s n) x)
    (hinj : ∀ n, Set.InjOn f (s n)) (g : E → ENNReal) (hg : Measurable g) :
    (∫⁻ y, ∑' n, (f '' s n).indicator g y ∂μ) =
      ∫⁻ x in ⋃ n, s n, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  have him : ∀ n, MeasurableSet (f '' s n) := fun n =>
    measurable_image_of_fderivWithin (hs n) (hf' n) (hinj n)
  rw [lintegral_tsum (fun n => (hg.indicator (him n)).aemeasurable)]
  simp_rw [lintegral_indicator (him _)]
  simp_rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hs _) (hf' _) (hinj _) g]
  exact (lintegral_iUnion hs hd (fun x => ENNReal.ofReal |(f' x).det| * g (f x))).symm

private theorem card_aux {α β : Type*} (f : α → β) (s : ℕ → Set α)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hinj : ∀ n, Set.InjOn f (s n)) (y : β) :
    ({x : α | x ∈ ⋃ n, s n ∧ f x = y}.encard : ENNReal) =
      ∑' n, (f '' s n).indicator (fun _ => (1 : ENNReal)) y := by
  classical
  let t : ℕ → Set α := fun n => {x | x ∈ s n ∧ f x = y}
  have heq : {x : α | x ∈ ⋃ n, s n ∧ f x = y} = ⋃ n, t n := by
    ext x
    simp only [t, Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  have hdt : Set.univ.PairwiseDisjoint t := by
    intro i hi j hj hij
    exact (hd hij).mono (fun x hx => hx.1) (fun x hx => hx.1)
  rw [heq, ← ENNReal.tsum_set_one, ENNReal.tsum_biUnion (f := fun _ : α => (1 : ENNReal)) hdt]
  apply tsum_congr
  intro n
  rw [ENNReal.tsum_set_one]
  by_cases hy : y ∈ f '' s n
  · obtain ⟨x, hx, hxy⟩ := hy
    have hy : y ∈ f '' s n := ⟨x, hx, hxy⟩
    have ht : t n = {x} := by
      ext z
      constructor
      · intro hz
        exact hinj n hz.1 hx (hz.2.trans hxy.symm)
      · rintro rfl
        exact ⟨hx, hxy⟩
    simp [ht, Set.indicator_of_mem hy]
  · have ht : t n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, hx.1, hx.2⟩
    simp [ht, Set.indicator_of_notMem hy]

theorem proof_SphereGeom_Aux_Crofton_lintegral_encard_fiber_partition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → E) (f' : E → E →L[ℝ] E)
    (s : ℕ → Set E) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hf' : ∀ n x, x ∈ s n → HasFDerivWithinAt f (f' x) (s n) x)
    (hinj : ∀ n, Set.InjOn f (s n)) :
    (∫⁻ y, ({x : E | x ∈ ⋃ n, s n ∧ f x = y}.encard : ENNReal) ∂μ) =
      ∫⁻ x in ⋃ n, s n, ENNReal.ofReal |(f' x).det| ∂μ := by
  simp_rw [card_aux f s hd hinj]
  simpa using area_aux
    μ f f' s hs hd hf' hinj (fun _ => (1 : ENNReal)) measurable_const
