import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_arc_inventory
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_arc_inventory :
    (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) =
  4*triangleSide 0 1 2 3 + 2*triangleSide 1 2 0 3 + 2*triangleSide 0 2 3 1 +
  2*triangleSide 0 3 2 1 + 2*triangleSide 2 3 0 1 +
  bulkSource 0 1 + 2*bulkSource 0 2 + 2*bulkSource 1 2 + bulkSource 2 3 + Ssliver :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_arc_inventory
