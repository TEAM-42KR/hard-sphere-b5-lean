import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_ae_encard_image_diff_countable
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.ae_encard_image_diff_countable :
    ∀ (γ : ℝ → E3) (S T : Set ℝ) (hT : T.Countable)
    (hs : ∀ s ∈ S, ‖γ s‖ = 1), (fun p : E3 => ((greatCircle p ∩ γ '' (S \ T)).encard : ENNReal)) =ᵐ[dOmega]
      (fun p : E3 => ((greatCircle p ∩ γ '' S).encard : ENNReal)) :=
  @proof_SphereGeom_Aux_Crofton_ae_encard_image_diff_countable
