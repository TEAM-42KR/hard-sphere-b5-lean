import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_no_near_sliver_on_diagonal
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.no_near_sliver_on_diagonal :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs : s < 1) (hXY : X = Y), 0 < P4poly X Y s :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_no_near_sliver_on_diagonal
