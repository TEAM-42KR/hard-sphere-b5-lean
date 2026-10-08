import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Cylinder_dOmega_normalize
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem SphereGeom.Aux.Cylinder.dOmega_normalize :
    dOmega = (3 : ENNReal) •
      (((volume : Measure E3).restrict (Metric.ball (0 : E3) 1 \ {0})).map
        (fun u : E3 => (‖u‖⁻¹ : ℝ) • u)) :=
  @proof_SphereGeom_Aux_Cylinder_dOmega_normalize
