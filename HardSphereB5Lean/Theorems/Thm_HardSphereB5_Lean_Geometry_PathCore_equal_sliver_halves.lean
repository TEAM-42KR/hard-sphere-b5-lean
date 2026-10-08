import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_equal_sliver_halves
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.equal_sliver_halves :
    nearCorrection 0 2=Ssliver/2 ∧ nearCorrection 1 3=Ssliver/2 ∧
  nearCorrection 0 1=0 ∧ nearCorrection 1 2=0 ∧ nearCorrection 0 3=0 ∧ nearCorrection 2 3=0 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_equal_sliver_halves
