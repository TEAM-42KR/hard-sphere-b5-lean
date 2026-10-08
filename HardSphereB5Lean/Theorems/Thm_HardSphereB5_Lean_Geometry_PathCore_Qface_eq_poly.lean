import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_Qface_eq_poly
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.Qface_eq_poly :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (l : Fin 4), Qface c l = Qpoly X Y s l :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_Qface_eq_poly
