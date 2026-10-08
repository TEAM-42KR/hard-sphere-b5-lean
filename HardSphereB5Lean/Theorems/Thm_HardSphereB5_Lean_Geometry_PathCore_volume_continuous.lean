import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_volume_continuous
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.volume_continuous :
    Continuous (fun c : Fin 4 → Pt => vol c Finset.univ) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_volume_continuous
