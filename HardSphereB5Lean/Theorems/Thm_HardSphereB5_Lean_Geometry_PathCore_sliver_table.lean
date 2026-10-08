import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_sliver_table
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.sliver_table :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0), (s < 1 → Y < X → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (2, 0, 2, 0) ∧ isCommon c 0 2) ∧
    (s < 1 → X < Y → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 2, 0, 2) ∧ isCommon c 1 3) ∧
    (1 < s → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 0, 2, 2) ∧ isCommon c 2 3) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_sliver_table
