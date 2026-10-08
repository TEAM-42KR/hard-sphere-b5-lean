import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_point_values :
    Hpoly (3 / 4) (1 / 4) (11 / 32) = 9 / 1024 ∧ P4poly (3 / 4) (1 / 4) (11 / 32) = -3 / 1024 := by
  constructor <;> norm_num [Hpoly, P4poly]

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_point_values
