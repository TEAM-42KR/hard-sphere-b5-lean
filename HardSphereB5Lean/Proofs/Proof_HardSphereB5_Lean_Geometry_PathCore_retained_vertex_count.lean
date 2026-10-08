import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_retained_vertex_count {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) : ∑ l, nRet c l = 4 := by
  rcases lt_or_gt_of_ne hP with hneg|hpos
  · exact (sliver_incidence hc hneg).2.1
  · simp only [(bulk_incidence hc hpos).1]
    simp

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_retained_vertex_count
