import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_pair_arc_normalizer (a b cc : ℝ) :
  DeltaT a b cc * (4-a) = a*(b+cc-a)^2+4*QT a b cc ∧
  (2*(a+b-cc)-a*b)^2+4*QT a b cc = a*b*(4-a)*(4-b) := by
  constructor <;> simp only [QT, DeltaT] <;> ring

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_pair_arc_normalizer
