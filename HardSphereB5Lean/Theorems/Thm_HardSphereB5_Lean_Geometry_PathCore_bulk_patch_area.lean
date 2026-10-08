import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_area
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.bulk_patch_area :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) (i : Fin 4), pArea c i Finset.univ = -π + (1 / 2) * ∑ l, (if l ≠ i then pArea c i (faceSet l) else 0)
      + (1 / 2) * ∑ j, (if j ≠ i then dist (c i) (c j) * phiE c i j else 0) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_area
