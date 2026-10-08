import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_moving_point_width
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.near_moving_point_width :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs : s < 1), phiE c 2 3 = atan2 (2 * √(s * Hpoly X Y s)) (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ∧
    (0 < P4poly X Y s → ell c 2 3 =
        atan2 (2 * √(Qpoly X Y s 1)) (√s * (1 + Y - s))
          + atan2 (2 * √(Qpoly X Y s 0)) (√s * (1 + X - s)) - phiE c 2 3) ∧
    (P4poly X Y s < 0 → Y < X → ell c 2 3 = 2 * atan2 (2 * √(Qpoly X Y s 1)) (√s * (1 + Y - s))) ∧
    (P4poly X Y s < 0 → X < Y → ell c 2 3 = 2 * atan2 (2 * √(Qpoly X Y s 0)) (√s * (1 + X - s))) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_moving_point_width
