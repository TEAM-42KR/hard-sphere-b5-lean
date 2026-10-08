import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_pathFaceQ_pos
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean

theorem HardSphereB5.Lean.Geometry.pathFaceQ_pos :
    ∀ (c : Fin 4 → Pt) (X Y s : ℝ)
    (h01 : dist (c 0) (c 1) ^ 2 = 1) (h02 : dist (c 0) (c 2) ^ 2 = 1)
    (h03 : dist (c 0) (c 3) ^ 2 = Y) (h12 : dist (c 1) (c 2) ^ 2 = X)
    (h13 : dist (c 1) (c 3) ^ 2 = 1) (h23 : dist (c 2) (c 3) ^ 2 = s)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k), 0 < 4 * dist (c i) (c j) ^ 2 * dist (c i) (c k) ^ 2
        - (dist (c i) (c j) ^ 2 + dist (c i) (c k) ^ 2 - dist (c j) (c k) ^ 2) ^ 2
        - dist (c i) (c j) ^ 2 * dist (c i) (c k) ^ 2 * dist (c j) (c k) ^ 2 :=
  @proof_HardSphereB5_Lean_Geometry_pathFaceQ_pos
