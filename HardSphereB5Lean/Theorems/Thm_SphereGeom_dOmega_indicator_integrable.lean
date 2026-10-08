import HardSphereB5Lean.Proofs.Proof_SphereGeom_dOmega_indicator_integrable
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.dOmega_indicator_integrable :
    ∀ (A : Set E3) (hA : MeasurableSet A), Integrable (A.indicator (fun _ : E3 => (1 : ℝ))) dOmega :=
  @proof_SphereGeom_dOmega_indicator_integrable
