import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped NNReal

theorem proof_SphereGeom_Aux_Crofton_exists_injective_partition_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → E) (f' : E → E →L[ℝ] E) (s : Set E) (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hreg : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∃ t : ℕ → Set E, (∀ n, MeasurableSet (t n)) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ (⋃ n, t n) = s ∧
      (∀ n, Set.InjOn f (t n)) ∧ (∀ n, t n ⊆ s) := by
  classical
  by_cases hempty : s = ∅
  · subst s
    refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i j hij; simp
    · simp
    · intro n; exact Set.injOn_empty f
    · simp
  have hne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  let radius : (E →L[ℝ] E) → ℝ≥0 := fun A =>
    if h : A.det = 0 then 1 else
      if hsub : Subsingleton E then 1 else
        ‖((A.toContinuousLinearEquivOfDetNeZero h).symm : E →L[ℝ] E)‖₊⁻¹ / 2
  have hrpos : ∀ A, radius A ≠ 0 := by
    intro A
    unfold radius
    split_ifs with hdet hsub
    · norm_num
    · norm_num
    · have hnn : ‖((A.toContinuousLinearEquivOfDetNeZero hdet).symm : E →L[ℝ] E)‖₊ ≠ 0 := by
        rw [ne_eq, nnnorm_eq_zero]
        intro hzero
        apply hsub
        refine ⟨fun x y => ?_⟩
        have hx : (A.toContinuousLinearEquivOfDetNeZero hdet).symm x = 0 := by
          change (((A.toContinuousLinearEquivOfDetNeZero hdet).symm : E →L[ℝ] E) x) = 0
          rw [hzero]; rfl
        have hy : (A.toContinuousLinearEquivOfDetNeZero hdet).symm y = 0 := by
          change (((A.toContinuousLinearEquivOfDetNeZero hdet).symm : E →L[ℝ] E) y) = 0
          rw [hzero]; rfl
        exact (A.toContinuousLinearEquivOfDetNeZero hdet).symm.injective (hx.trans hy.symm)
      exact div_ne_zero (inv_ne_zero hnn) (by norm_num)
  obtain ⟨t, A, hd, hm, hc, ha, hvals⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' radius hrpos
  refine ⟨fun n => s ∩ t n, fun n => hs.inter (hm n),
    pairwise_disjoint_mono hd (fun n => Set.inter_subset_right), ?_, ?_, fun _ => Set.inter_subset_left⟩
  · rw [← Set.inter_iUnion]
    exact Set.inter_eq_left.mpr hc
  · intro n
    obtain ⟨y, hy, hAy⟩ := hvals hne n
    have hAn : (A n).det ≠ 0 := by rw [hAy]; exact hreg y hy
    let e := (A n).toContinuousLinearEquivOfDetNeZero hAn
    have happrox : ApproximatesLinearOn f (e : E →L[ℝ] E) (s ∩ t n) (radius (A n)) := by
      simpa only [e, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using ha n
    apply happrox.injOn
    by_cases hsub : Subsingleton E
    · exact Or.inl hsub
    · refine Or.inr ?_
      simp only [radius, dif_neg hAn, dif_neg hsub]
      have hnn : 0 < ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ := by
        apply inv_pos.mpr
        rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
        intro hzero
        apply hsub
        refine ⟨fun x y => e.symm.injective ?_⟩
        have hx : e.symm x = 0 := by change ((e.symm : E →L[ℝ] E) x) = 0; rw [hzero]; rfl
        have hy : e.symm y = 0 := by change ((e.symm : E →L[ℝ] E) y) = 0; rw [hzero]; rfl
        exact hx.trans hy.symm
      exact half_lt_self hnn
