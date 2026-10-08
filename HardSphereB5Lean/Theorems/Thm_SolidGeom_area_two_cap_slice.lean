import HardSphereB5Lean.Proofs.Proof_SolidGeom_area_two_cap_slice
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SolidGeom.area_two_cap_slice :
    ∀ (x y z : E3)
    (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
      - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2),
    let a := dist x y ^ 2
    let b := dist x z ^ 2
    let c := dist y z ^ 2
    let k := Real.sqrt a / 2
    let l := Real.sqrt b / 2
    let alpha := Real.arccos ((a + b - c) / (2 * Real.sqrt a * Real.sqrt b))
    let H := min (Real.sqrt (1 - k ^ 2)) (Real.sqrt (1 - l ^ 2))
    let f := fun t : ℝ => Real.arccos (k / Real.sqrt (1 - t ^ 2))
    let g := fun t : ℝ => Real.arccos (l / Real.sqrt (1 - t ^ 2))
    (sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1)).toReal =
      2 * (∫ t in (0 : ℝ)..H, max 0 (min (2 * f t) (min (2 * g t) (f t + g t - alpha)))) :=
  @proof_SolidGeom_area_two_cap_slice
