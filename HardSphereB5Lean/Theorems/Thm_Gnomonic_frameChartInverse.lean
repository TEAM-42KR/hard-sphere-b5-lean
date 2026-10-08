import HardSphereB5Lean.Proofs.Proof_Gnomonic_frameChartInverse
import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
set_option autoImplicit false
open MeasureTheory SphereGeom Gnomonic

theorem Gnomonic.frameChartInverse :
    ∀ (R : E3 ≃ₗᵢ[ℝ] E3), Measurable (inverseFrame R) ∧
  (∀ u ∈ hemisphereFrame R, inverseFrame R (chartFrame R u) = u) ∧
  (∀ x, chartFrame R (inverseFrame R x) = x) :=
  @proof_Gnomonic_frameChartInverse
