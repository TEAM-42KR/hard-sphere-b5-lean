import HardSphereB5Lean.Proofs.Proof_Gnomonic_integralFromChartMeasure
import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
set_option autoImplicit false
open MeasureTheory SphereGeom Gnomonic

theorem Gnomonic.integralFromChartMeasure :
    ∀ (R : E3 ≃ₗᵢ[ℝ] E3)
    (hm : Measurable (inverseFrame R))
    (hleft : ∀ u ∈ hemisphereFrame R, inverseFrame R (chartFrame R u) = u)
    (hright : ∀ x, chartFrame R (inverseFrame R x) = x)
    (hchart : planarMeasure.map (inverseFrame R) = dOmega.restrict (hemisphereFrame R))
    (U : Set E3) (hU : MeasurableSet U) (hsub : U ⊆ hemisphereFrame R)
    (f : E3 → ℝ) (hf : IntegrableOn f U dOmega), ∫ u in U, f u ∂dOmega =
      ∫ x in chartFrame R '' U, density x * f (inverseFrame R x) :=
  @proof_Gnomonic_integralFromChartMeasure
