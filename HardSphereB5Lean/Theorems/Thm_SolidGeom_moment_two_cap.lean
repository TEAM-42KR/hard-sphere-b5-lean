import HardSphereB5Lean.Proofs.Proof_SolidGeom_moment_two_cap
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.moment_two_cap :
    ∀ (x y z : E3)
    (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
        - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2),
    let a := dist x y ^ 2
    let b := dist x z ^ 2
    let cc := dist y z ^ 2
    let Δ := 4 * a * b - (a + b - cc) ^ 2
    let Q := Δ - a * b * cc
    ∫ u in Metric.closedBall y 1 ∩ Metric.closedBall z 1, (u - x) ∂(sphereMeasure x) =
      ((1 - a / 4) / √a * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩) • (y - x)
        + ((1 - b / 4) / √b * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩) • (z - x)
        + (√Q / Δ) • cross ((y - x) - (z - x)) (cross (y - x) (z - x)) :=
  @proof_SolidGeom_moment_two_cap
