import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_lintegral_encard_greatCircle_image
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.lintegral_encard_greatCircle_image :
    ∀ (γ : ℝ → E3) (a b : ℝ)
    (hγ : ContDiff ℝ 1 γ) (hs : ∀ t ∈ Set.Icc a b, ‖γ t‖ = 1)
    (hreg : ∀ t ∈ Set.Icc a b, deriv γ t ≠ 0) (hinj : Set.InjOn γ (Set.Icc a b))
    (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b), ∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega =
      4 * ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ :=
  @proof_SphereGeom_Aux_Crofton_lintegral_encard_greatCircle_image
