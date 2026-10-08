import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_weighted_apex_coefficient
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.weighted_apex_coefficient :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), Lapex c 3 0 2 = (2*Y*s-Y^2-s^2+Y+s)/(4*Y*s-(Y+s-1)^2) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_weighted_apex_coefficient
