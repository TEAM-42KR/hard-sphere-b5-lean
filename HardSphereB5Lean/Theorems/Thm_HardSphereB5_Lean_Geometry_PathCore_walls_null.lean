import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_walls_null
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.walls_null :
    volume wallSet = 0 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_walls_null
