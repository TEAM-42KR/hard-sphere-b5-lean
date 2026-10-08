import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_counts
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_selector_counts :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s ≠ 0), ((Bminus Y s<X → nearCounts c=(1,1)) ∧
   (X<Bminus Y s → s<s0 Y → nearCounts c=(2,0)) ∧
   (X<Bminus Y s → s0 Y<s → nearCounts c=(0,2))) ∧
  (Bminus Y s<X ∨ (X<Bminus Y s ∧ s<s0 Y) ∨ (X<Bminus Y s ∧ s0 Y<s)) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_counts
