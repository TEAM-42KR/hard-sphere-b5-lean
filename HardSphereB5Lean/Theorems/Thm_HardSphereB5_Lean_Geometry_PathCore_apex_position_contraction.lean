import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_apex_position_contraction
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.apex_position_contraction :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), (∑ i, ∑ l, (if l≠i then inner ℝ (c i) (apexTerm c i l) else 0)) = -√(Hpoly X Y s)/4 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_apex_position_contraction
