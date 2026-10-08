import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_adjacent_unit_halfwidths
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.adjacent_unit_halfwidths :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), betaA c 0 1 2=betaA c 0 2 1 ∧ betaA c 0 1 3=betaA c 1 3 0 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_adjacent_unit_halfwidths
