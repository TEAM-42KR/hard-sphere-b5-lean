import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_point_values
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.obtuse_point_values :
    Hpoly (3 / 4) (1 / 4) (11 / 32) = 9 / 1024 ∧ P4poly (3 / 4) (1 / 4) (11 / 32) = -3 / 1024 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_point_values
