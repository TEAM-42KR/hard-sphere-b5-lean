import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_factorization
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_selector_factorization :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s ≠ 0), P4poly X Y s = Y*(4-Y)*(X-Bminus Y s)*(Bplus Y s-X) ∧
  1 < Bplus Y s ∧ (0<P4poly X Y s ↔ Bminus Y s<X) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_factorization
