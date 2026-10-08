import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_common_pair_acute_obtuse
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_common_pair_acute_obtuse :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s)
    (hs : s < 1) (hP : P4poly X Y s < 0), (Y < X → betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3) ∧
    (X < Y → betaA c 1 3 0 < π / 2 ∧ π / 2 < betaA c 1 3 2) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_common_pair_acute_obtuse
