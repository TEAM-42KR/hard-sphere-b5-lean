import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.nRet_coordinate_selector :
    ∀ (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (l : Fin 4), nRet c l = if 0 < P4poly X Y s then 1 else if Apoly X Y s l < 0 then 2 else 0 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector
