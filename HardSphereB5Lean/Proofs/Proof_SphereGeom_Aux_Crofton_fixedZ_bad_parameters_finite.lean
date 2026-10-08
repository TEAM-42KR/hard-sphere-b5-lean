import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_fixedZ_bad_parameters_finite (γ : ℝ → E3) (a b : ℝ)
    (hs : ∀ s ∈ Set.Icc a b, ‖γ s‖ = 1) (hinj : Set.InjOn γ (Set.Icc a b)) :
    {s : ℝ | s ∈ Set.Icc a b ∧ (γ s) 0 ^ 2 + (γ s) 1 ^ 2 = 0}.Finite := by
  let ez : E3 := WithLp.toLp 2 ![0, 0, 1]
  let B : Set ℝ := {s | s ∈ Set.Icc a b ∧ (γ s) 0 ^ 2 + (γ s) 1 ^ 2 = 0}
  change B.Finite
  have hb : γ '' B ⊆ ({ez, -ez} : Set E3) := by
    rintro p ⟨s, hss, rfl⟩
    have hn := hs s hss.1
    have h0 : (γ s) 0 = 0 := by nlinarith [sq_nonneg ((γ s) 0), sq_nonneg ((γ s) 1), hss.2]
    have h1 : (γ s) 1 = 0 := by nlinarith [sq_nonneg ((γ s) 0), sq_nonneg ((γ s) 1), hss.2]
    have hnorm : (γ s) 0 ^ 2 + (γ s) 1 ^ 2 + (γ s) 2 ^ 2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, hn, add_assoc] using
        (EuclideanSpace.real_norm_sq_eq (γ s)).symm
    have hsq : (γ s) 2 ^ 2 = (1 : ℝ) ^ 2 := by nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hp | hp
    · left
      apply PiLp.ext
      intro i
      fin_cases i <;> simpa [ez, h0, h1, hp]
    · right
      apply PiLp.ext
      intro i
      fin_cases i <;> simpa [ez, h0, h1, hp]
  exact ((Set.toFinite ({ez, -ez} : Set E3)).subset hb).of_finite_image
    (hinj.mono (fun s h => h.1))
