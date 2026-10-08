import HardSphereB5Lean.Proofs.Proof_SolidGeom_area_two_cap
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.area_two_cap :
    ∀ (x y z : E3)
    (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
        - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2),
    let a := dist x y ^ 2
    let b := dist x z ^ 2
    let cc := dist y z ^ 2
    let Q := 4 * a * b - (a + b - cc) ^ 2 - a * b * cc
    (sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1)).toReal =
      2 * π - 2 * Complex.arg ⟨2 * (a + b - cc) - a * b, 2 * √Q⟩
        - √a * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩
        - √b * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩ :=
  @proof_SolidGeom_area_two_cap
