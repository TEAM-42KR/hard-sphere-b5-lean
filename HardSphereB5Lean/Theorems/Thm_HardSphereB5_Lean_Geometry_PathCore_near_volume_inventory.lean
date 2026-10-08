import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_volume_inventory
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_volume_inventory :
    Kcap=2*Vadj+2*Vnon+Ccap+Dcap+2*Eadj+2*Enon +
  (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_volume_inventory
