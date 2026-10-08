import HardSphereB5Lean.Proofs.Proof_SolidGeom_area_moment_pair_cap
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.area_moment_pair_cap :
    ∀ (x y : E3) (h0 : 0 < dist x y) (h2 : dist x y < 2), (sphereMeasure x (Metric.closedBall y 1)).toReal = 2 * π * (1 - dist x y / 2) ∧
      ∫ u in Metric.closedBall y 1, (u - x) ∂(sphereMeasure x) =
        (π * (1 - dist x y ^ 2 / 4) / dist x y) • (y - x) :=
  @proof_SolidGeom_area_moment_pair_cap
