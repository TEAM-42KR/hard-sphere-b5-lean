import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_sliver_patch_valuation
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.sliver_patch_valuation :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j) (m : Fin 4), pArea c m Finset.univ =
        pArea c m {i, j, oth1 i j} + pArea c m {i, j, oth2 i j} - pArea c m {i, j} ∧
      pMoment c m Finset.univ =
        pMoment c m {i, j, oth1 i j} + pMoment c m {i, j, oth2 i j} - pMoment c m {i, j} :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_sliver_patch_valuation
