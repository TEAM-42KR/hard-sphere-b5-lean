import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_circumcenter_unique
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.circumcenter_unique :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), ∃! O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4*Hpoly X Y s) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_circumcenter_unique
