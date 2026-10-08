import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_midpoint_values
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.midpoint_values :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s),
    let M := (1/2 : ℝ) • (c 0+c 1)
  dist M (c 0)^2=1/4 ∧ dist M (c 1)^2=1/4 ∧
  dist M (c 2)^2=(1+2*X)/4 ∧ dist M (c 3)^2=(1+2*Y)/4 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_midpoint_values
