import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section

theorem proof_SphereGeom_Aux_Santalo_rectangle_FTC
    (Q Q2 Q12 : ℝ → ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hprod : Integrable (Function.uncurry Q12)
      (((volume : Measure ℝ).restrict (Set.Ioc a b)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc c d))))
    (hcont : ∀ y ∈ Set.Ioo c d, ContinuousOn (fun x => Q2 x y) (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo c d, ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun s => Q2 s y) (Q12 x y) x)
    (hint : ∀ y ∈ Set.Ioo c d, IntervalIntegrable (fun x => Q12 x y) volume a b)
    (hedge : ∀ x ∈ ({a, b} : Set ℝ), ContinuousOn (Q x) (Set.Icc c d))
    (hDedge : ∀ x ∈ ({a, b} : Set ℝ), ∀ y ∈ Set.Ioo c d,
      HasDerivAt (Q x) (Q2 x y) y)
    (hIedge : ∀ x ∈ ({a, b} : Set ℝ), IntervalIntegrable (Q2 x) volume c d) :
    (∫ x in a..b, ∫ y in c..d, Q12 x y) = Q b d - Q b c - Q a d + Q a c := by
  have ha : a ∈ ({a, b} : Set ℝ) := by simp
  have hb : b ∈ ({a, b} : Set ℝ) := by simp
  have hslice : (fun y => ∫ x in a..b, Q12 x y) =ᵐ[volume.restrict (Set.Ioc c d)]
      (fun y => Q2 b y - Q2 a y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne d)] with y hy hne
    have hy' : y ∈ Set.Ioo c d := ⟨hy.1, lt_of_le_of_ne hy.2 hne⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (hcont y hy') (hderiv y hy') (hint y hy')
  have heqa : (∫ y in c..d, Q2 a y) = Q a d - Q a c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd
      (hedge a ha) (hDedge a ha) (hIedge a ha)
  have heqb : (∫ y in c..d, Q2 b y) = Q b d - Q b c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd
      (hedge b hb) (hDedge b hb) (hIedge b hb)
  calc
    (∫ x in a..b, ∫ y in c..d, Q12 x y) =
        ∫ y in c..d, ∫ x in a..b, Q12 x y := by
      simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
      exact integral_integral_swap hprod
    _ = ∫ y in c..d, Q2 b y - Q2 a y := by
      rw [intervalIntegral.integral_of_le hcd, intervalIntegral.integral_of_le hcd]
      exact integral_congr_ae hslice
    _ = (∫ y in c..d, Q2 b y) - (∫ y in c..d, Q2 a y) :=
      intervalIntegral.integral_sub (hIedge b hb) (hIedge a ha)
    _ = Q b d - Q b c - Q a d + Q a c := by rw [heqa, heqb]; ring
