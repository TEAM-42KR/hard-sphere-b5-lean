import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_walls_null
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_walls_pathMeasure_null_of_deps : pathMeasure wallSet = 0 := by
  unfold pathMeasure
  apply withDensity_absolutelyContinuous
  apply le_antisymm _ bot_le
  exact (Measure.restrict_apply_le support wallSet).trans_eq walls_null
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_walls_pathMeasure_null : pathMeasure wallSet = 0 := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_walls_pathMeasure_null_of_deps

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_walls_pathMeasure_null
