import HardSphereB5Lean.Proofs.Proof_SphereGeom_lintegral_arcMeasure_greatCircle
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.lintegral_arcMeasure_greatCircle :
    ∀ (A : Set E3) (hA : MeasurableSet A)
    (hAs : A ⊆ Metric.sphere (0 : E3) 1), ∫⁻ p, arcMeasure (greatCircle p ∩ A) ∂dOmega = ENNReal.ofReal (2 * Real.pi) * dOmega A :=
  @proof_SphereGeom_lintegral_arcMeasure_greatCircle
