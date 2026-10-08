import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_threeBallVolume
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean

theorem HardSphereB5.Lean.Geometry.threeBallVolume :
    ∀ (c : Fin 4 → Pt) (X Y s : ℝ)
    (h01 : dist (c 0) (c 1) ^ 2 = 1) (h02 : dist (c 0) (c 2) ^ 2 = 1)
    (h03 : dist (c 0) (c 3) ^ 2 = Y) (h12 : dist (c 1) (c 2) ^ 2 = X)
    (h13 : dist (c 1) (c 3) ^ 2 = 1) (h23 : dist (c 2) (c 3) ^ 2 = s)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    let a := dist (c i) (c j) ^ 2
    let b := dist (c i) (c k) ^ 2
    let cc := dist (c j) (c k) ^ 2
    let Q := 4 * a * b - (a + b - cc) ^ 2 - a * b * cc
    let g : ℝ → ℝ := fun d => d - d ^ 3 / 12
    (volume (Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 ∩ Metric.closedBall (c k) 1)).toReal =
      2 * π - 2 / 3 * (Complex.arg ⟨2 * (a + b - cc) - a * b, 2 * √Q⟩
          + Complex.arg ⟨2 * (a + cc - b) - a * cc, 2 * √Q⟩
          + Complex.arg ⟨2 * (b + cc - a) - b * cc, 2 * √Q⟩)
        - (g (√a) * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩
          + g (√b) * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩
          + g (√cc) * Complex.arg ⟨√cc * (a + b - cc), 2 * √Q⟩)
        + √Q / 6 :=
  @proof_HardSphereB5_Lean_Geometry_threeBallVolume
