import Mathlib
set_option autoImplicit false

theorem proof_SphereGeom_Aux_Arrangement_trig_zeros_finite (α β γ p q : ℝ)
    (hnonzero : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) :
    {t ∈ Set.Icc p q | α * Real.cos t + β * Real.sin t - γ = 0}.Finite := by
  let f : ℝ → ℝ := fun t => α * Real.cos t + β * Real.sin t - γ
  have hf : AnalyticOnNhd ℝ f Set.univ := by
    intro t _
    exact ((analyticAt_const.mul Real.analyticAt_cos).add
      (analyticAt_const.mul Real.analyticAt_sin)).sub analyticAt_const
  have hn : ¬ Set.EqOn f 0 Set.univ := by
    intro hzero
    have h0 := hzero (Set.mem_univ (0 : ℝ))
    have hp := hzero (Set.mem_univ Real.pi)
    have hp2 := hzero (Set.mem_univ (Real.pi / 2))
    simp [f] at h0 hp hp2
    have ha : α = 0 := by linarith
    have hg : γ = 0 := by linarith
    have hb : β = 0 := by linarith
    rcases hnonzero with h | h | h
    · exact h ha
    · exact h hb
    · exact h hg
  have hc : ∀ᶠ t in Filter.codiscreteWithin (Set.univ : Set ℝ), f t ≠ 0 :=
    (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left hn
  have hmem : {t : ℝ | f t ≠ 0} ∈ Filter.codiscreteWithin (Set.Icc p q) :=
    Filter.codiscreteWithin_mono (Set.subset_univ (Set.Icc p q)) hc
  have hfinite := isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin hmem
  have hset : Set.Icc p q \ {t : ℝ | f t ≠ 0} =
      {t ∈ Set.Icc p q | α * Real.cos t + β * Real.sin t - γ = 0} := by
    ext t
    simp [f]
  rw [hset] at hfinite
  exact hfinite
