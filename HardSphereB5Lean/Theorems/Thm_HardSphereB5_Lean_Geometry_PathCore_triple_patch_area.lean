import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_triple_patch_area
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.triple_patch_area :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k), pArea c i {i, j, k} =
      2 * π - 2 * gammaA c i j k - √(q c i j) * betaA c i j k - √(q c i k) * betaA c i k j :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_triple_patch_area
