import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_bulk_apex_anchor
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.bulk_apex_anchor :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i l r : Fin 4) (hil : i≠l), inner ℝ (c r-c i) (apexTerm c i l) =
    if r=l then √(Hpoly X Y s)*Lapex c i (oth1 i l) (oth2 i l)/8 else 0 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_bulk_apex_anchor
