import HardSphereB5Lean.Proofs.Proof_Gnomonic_integralFrame
import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
set_option autoImplicit false
open MeasureTheory SphereGeom Gnomonic

theorem Gnomonic.integralFrame :
    ∀ (R : E3 ≃ₗᵢ[ℝ] E3)
  (U : Set E3) (hU : MeasurableSet U) (hsub : U ⊆ hemisphereFrame R)
  (f : E3 → ℝ) (hf : IntegrableOn f U dOmega), ∫ u in U, f u ∂dOmega = ∫ x in chartFrame R '' U,
    density x * f (inverseFrame R x) :=
  @proof_Gnomonic_integralFrame
