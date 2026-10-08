import HardSphereB5Lean.Proofs.Proof_Gnomonic_chartMeasure
import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
set_option autoImplicit false
open MeasureTheory SphereGeom Gnomonic

theorem Gnomonic.chartMeasure :
    ∀ (R : E3 ≃ₗᵢ[ℝ] E3), planarMeasure.map (inverseFrame R) = dOmega.restrict (hemisphereFrame R) :=
  @proof_Gnomonic_chartMeasure
