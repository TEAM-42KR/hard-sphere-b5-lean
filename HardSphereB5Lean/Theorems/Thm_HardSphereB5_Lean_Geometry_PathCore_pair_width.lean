import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_pair_width
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.pair_width :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i j : Fin 4) (hij : i ≠ j), ell c i j = (nRet c (oth2 i j) : ℝ) * betaA c i j (oth1 i j)
        + (nRet c (oth1 i j) : ℝ) * betaA c i j (oth2 i j)
        - (if 0 < P4poly X Y s then phiE c i j else 0)
        - (if P4poly X Y s < 0 ∧ isCommon c i j then 2 * π else 0) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_pair_width
