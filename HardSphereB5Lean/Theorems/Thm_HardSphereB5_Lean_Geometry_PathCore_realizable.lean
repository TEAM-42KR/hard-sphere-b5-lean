import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_realizable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.realizable :
    ∀ {X : ℝ} {Y : ℝ} {s : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s), ∃ c : Fin 4 → Pt, IsPathConfig c X Y s :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_realizable
