import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_lintegral_encard_with_frame
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.lintegral_encard_with_frame :
    ∀ (γ a b : ℝ → E3) (S : Set ℝ) (hS : MeasurableSet S)
    (hma : Measurable a) (hmb : Measurable b) (hmγ : Measurable γ)
    (hs : ∀ s ∈ S, ‖γ s‖ = 1) (hinj : Set.InjOn γ S)
    (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, γ s] ∧ cross (a s) (b s) = γ s)
    (hda : ∀ s ∈ S, DifferentiableAt ℝ a s)
    (hdb : ∀ s ∈ S, DifferentiableAt ℝ b s)
    (hdγ : ∀ s ∈ S, DifferentiableAt ℝ γ s)
    (hoa : ∀ s ∈ S, (fun t => inner ℝ (a t) (γ t)) =ᶠ[nhds s] (fun _ => 0))
    (hob : ∀ s ∈ S, (fun t => inner ℝ (b t) (γ t)) =ᶠ[nhds s] (fun _ => 0))
    (htan : ∀ s ∈ S, inner ℝ (deriv γ s) (γ s) = 0)
    (hN : Measurable (fun p : E3 => ((greatCircle p ∩ γ '' S).encard : ENNReal))), ∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega =
      4 * ∫⁻ s in S, ENNReal.ofReal ‖deriv γ s‖ :=
  @proof_SphereGeom_Aux_Crofton_lintegral_encard_with_frame
