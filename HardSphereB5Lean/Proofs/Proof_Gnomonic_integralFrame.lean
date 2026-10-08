import HardSphereB5Lean.Theorems.Thm_Gnomonic_integralFromChartMeasure
import HardSphereB5Lean.Theorems.Thm_Gnomonic_frameChartInverse
import HardSphereB5Lean.Theorems.Thm_Gnomonic_chartMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom Gnomonic
noncomputable section

theorem proof_Gnomonic_integralFrame (R : E3 ≃ₗᵢ[ℝ] E3)
  (U : Set E3) (hU : MeasurableSet U) (hsub : U ⊆ hemisphereFrame R)
  (f : E3 → ℝ) (hf : IntegrableOn f U dOmega) :
  ∫ u in U, f u ∂dOmega = ∫ x in chartFrame R '' U,
    density x * f (inverseFrame R x) := by
  obtain ⟨hm,hl,hr⟩ := frameChartInverse R
  exact integralFromChartMeasure R hm hl hr (chartMeasure R) U hU hsub f hf
