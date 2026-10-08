import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_no_sliver_at_s_one
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.no_sliver_at_s_one :
    ∀ {X : ℝ} {Y : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1), 0 < P4poly X Y 1 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_no_sliver_at_s_one
