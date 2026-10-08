import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_moment
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.bulk_patch_moment :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) (i : Fin 4), pMoment c i Finset.univ =
      (1 / 2 : ℝ) • ∑ l, (if l ≠ i then pMoment c i (faceSet l) else 0)
        - (1 / 2 : ℝ) • ∑ j, (if j ≠ i then
            ((1 - q c i j / 4) / √(q c i j) * phiE c i j) • (c j - c i) else 0)
        + ∑ l, (if l ≠ i then apexTerm c i l else 0) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_moment
