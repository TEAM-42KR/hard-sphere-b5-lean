import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_sliver_order
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_selector_sliver_order :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s<0), (Y<X ↔ s<s0 Y) ∧ (X<Y ↔ s0 Y<s) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_sliver_order
