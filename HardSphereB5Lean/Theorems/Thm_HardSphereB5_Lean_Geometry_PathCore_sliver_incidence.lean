import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.sliver_incidence :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0), (∀ l, nRet c l = if 0 < Qpoly X Y s l ∧ Apoly X Y s l < 0 then 2 else 0) ∧
      ∑ l, nRet c l = 4 ∧
      ∃ i j, i ≠ j ∧ isCommon c i j ∧
        ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = if m = i ∨ m = j then 4 else 2 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
