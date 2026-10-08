import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_common_pair_halfwidth_sum
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.common_pair_halfwidth_sum :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s)
    (hP : P4poly X Y s < 0) (i j : Fin 4) (hij : i ≠ j) (hcom : isCommon c i j), π < betaA c i j (oth1 i j) + betaA c i j (oth2 i j) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_common_pair_halfwidth_sum
