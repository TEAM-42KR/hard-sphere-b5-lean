import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_pair23_halfwidths_acute
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_pair23_halfwidths_acute :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs : s < 1), betaA c 2 3 0 < π / 2 ∧ betaA c 2 3 1 < π / 2 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_pair23_halfwidths_acute
