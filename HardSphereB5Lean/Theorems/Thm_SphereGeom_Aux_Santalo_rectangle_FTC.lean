import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_rectangle_FTC
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Santalo.rectangle_FTC :
    ∀ (Q Q2 Q12 : ℝ → ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
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
    (hIedge : ∀ x ∈ ({a, b} : Set ℝ), IntervalIntegrable (Q2 x) volume c d), (∫ x in a..b, ∫ y in c..d, Q12 x y) = Q b d - Q b c - Q a d + Q a c :=
  @proof_SphereGeom_Aux_Santalo_rectangle_FTC
