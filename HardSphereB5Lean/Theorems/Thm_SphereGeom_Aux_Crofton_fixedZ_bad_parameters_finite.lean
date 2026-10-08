import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_fixedZ_bad_parameters_finite
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.fixedZ_bad_parameters_finite :
    ∀ (γ : ℝ → E3) (a b : ℝ)
    (hs : ∀ s ∈ Set.Icc a b, ‖γ s‖ = 1) (hinj : Set.InjOn γ (Set.Icc a b)), {s : ℝ | s ∈ Set.Icc a b ∧ (γ s) 0 ^ 2 + (γ s) 1 ^ 2 = 0}.Finite :=
  @proof_SphereGeom_Aux_Crofton_fixedZ_bad_parameters_finite
