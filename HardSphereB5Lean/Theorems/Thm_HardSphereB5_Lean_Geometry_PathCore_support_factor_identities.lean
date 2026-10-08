import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_support_factor_identities
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.support_factor_identities :
    ∀ (X Y : ℝ) (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1), (a0 X Y) ^ 2 - (b0 X Y) ^ 2 = (1-X)*(1-Y)+X*(1-Y)^2+Y*(1-X)^2 ∧
  (3-a0 X Y) ^ 2 - (b0 X Y) ^ 2 = (1-X)*(4-X*Y)+X*(1-Y)*(4-Y) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_support_factor_identities
