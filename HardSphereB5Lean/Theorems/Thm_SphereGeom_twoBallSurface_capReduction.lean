import HardSphereB5Lean.Proofs.Proof_SphereGeom_twoBallSurface_capReduction
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.twoBallSurface_capReduction :
    ∀ (x y z : E3), sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1) =
    dOmega (cap (y - x) (‖y - x‖ ^ 2 / 2) ∩ cap (z - x) (‖z - x‖ ^ 2 / 2)) ∧
  (∫ u in Metric.closedBall y 1 ∩ Metric.closedBall z 1, (u - x) ∂(sphereMeasure x)) =
    ∫ u in cap (y - x) (‖y - x‖ ^ 2 / 2) ∩ cap (z - x) (‖z - x‖ ^ 2 / 2), u ∂dOmega :=
  @proof_SphereGeom_twoBallSurface_capReduction
