import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_ArcLength_arcMeasure_image_regular
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.ArcLength.arcMeasure_image_regular :
    ∀ (γ : ℝ → E3) (a b : ℝ)
    (hγ : ContDiff ℝ 1 γ) (hreg : ∀ t ∈ Set.Icc a b, deriv γ t ≠ 0)
    (hinj : Set.InjOn γ (Set.Icc a b)) (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b), arcMeasure (γ '' S) = ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ :=
  @proof_SphereGeom_Aux_ArcLength_arcMeasure_image_regular
