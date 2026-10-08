import HardSphereB5Lean.Proofs.Proof_SolidGeom_volume_lens_closed
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.volume_lens_closed :
    ∀ (x y : E3) (h : dist x y ≤ 2), (volume (Metric.closedBall x 1 ∩ Metric.closedBall y 1)).toReal =
      π * (4 / 3 - dist x y + dist x y ^ 3 / 12) :=
  @proof_SolidGeom_volume_lens_closed
