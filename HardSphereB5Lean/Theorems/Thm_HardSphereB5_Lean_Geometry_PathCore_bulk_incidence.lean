import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.bulk_incidence :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s), (∀ l, nRet c l = 1) ∧ ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
