import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_chart5_ae_linear_ne
    (L : Chart5 →ₗ[ℝ] ℝ) (hL : L ≠ 0) (c : ℝ) : ∀ᵐ y : Chart5 ∂volume, L y ≠ c := by
  obtain ⟨u,hu⟩ : ∃ u : Chart5, L u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hL
    ext u
    exact h u
  let v : Chart5 := (c / L u) • u
  have hv : L v = c := by
    simp only [v,map_smul,smul_eq_mul]
    field_simp [hu]
  have hker : L.ker ≠ ⊤ := by
    intro h
    exact hL (LinearMap.ker_eq_top.mp h)
  have hk : ∀ᵐ y : Chart5 ∂volume, L y ≠ 0 := by
    rw [ae_iff]
    simp only [not_not]
    change volume {y : Chart5 | L y = 0} = 0
    exact Measure.addHaar_submodule (volume : Measure Chart5) L.ker hker
  have hs := (measurePreserving_add_right (volume : Measure Chart5) (-v)).quasiMeasurePreserving.ae hk
  filter_upwards [hs] with y hy
  intro heq
  apply hy
  simp only [map_add,map_neg,hv,heq,add_neg_cancel]
