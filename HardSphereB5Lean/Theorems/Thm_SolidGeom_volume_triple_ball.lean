import HardSphereB5Lean.Proofs.Proof_SolidGeom_volume_triple_ball
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.volume_triple_ball :
    ∀ (c : Fin 3 → E3)
    (hQ : 0 < 4 * dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2
        - (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 2) ^ 2 - dist (c 1) (c 2) ^ 2) ^ 2
        - dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2 * dist (c 1) (c 2) ^ 2),
    let a := dist (c 0) (c 1) ^ 2
    let b := dist (c 0) (c 2) ^ 2
    let cc := dist (c 1) (c 2) ^ 2
    let Q := 4 * a * b - (a + b - cc) ^ 2 - a * b * cc
    let g : ℝ → ℝ := fun d => d - d ^ 3 / 12
    (volume (Metric.closedBall (c 0) 1 ∩ Metric.closedBall (c 1) 1 ∩ Metric.closedBall (c 2) 1)).toReal =
      2 * π - 2 / 3 * (Complex.arg ⟨2 * (a + b - cc) - a * b, 2 * √Q⟩
          + Complex.arg ⟨2 * (a + cc - b) - a * cc, 2 * √Q⟩
          + Complex.arg ⟨2 * (b + cc - a) - b * cc, 2 * √Q⟩)
        - (g (√a) * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩
          + g (√b) * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩
          + g (√cc) * Complex.arg ⟨√cc * (a + b - cc), 2 * √Q⟩)
        + √Q / 6 :=
  @proof_SolidGeom_volume_triple_ball
