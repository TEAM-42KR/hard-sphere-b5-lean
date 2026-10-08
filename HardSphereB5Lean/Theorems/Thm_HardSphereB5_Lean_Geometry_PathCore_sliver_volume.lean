import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_sliver_volume
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.sliver_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j), vol c Finset.univ = vol c {i, j, oth1 i j} + vol c {i, j, oth2 i j} - V2 (dist (c i) (c j)) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_sliver_volume
