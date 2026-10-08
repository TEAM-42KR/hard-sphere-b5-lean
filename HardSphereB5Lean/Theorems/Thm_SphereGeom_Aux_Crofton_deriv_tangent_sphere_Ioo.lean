import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_deriv_tangent_sphere_Ioo
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.deriv_tangent_sphere_Ioo :
    ∀ (γ : ℝ → E3) (a b s : ℝ)
    (hs : ∀ t ∈ Set.Icc a b, ‖γ t‖ = 1)
    (hγ : DifferentiableAt ℝ γ s) (hst : s ∈ Set.Ioo a b), inner ℝ (deriv γ s) (γ s) = 0 :=
  @proof_SphereGeom_Aux_Crofton_deriv_tangent_sphere_Ioo
