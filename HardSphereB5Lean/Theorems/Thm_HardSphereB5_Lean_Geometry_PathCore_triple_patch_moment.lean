import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_triple_patch_moment
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.triple_patch_moment :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k), pMoment c i {i, j, k} =
      ((1 - q c i j / 4) / √(q c i j) * betaA c i j k) • (c j - c i)
        + ((1 - q c i k / 4) / √(q c i k) * betaA c i k j) • (c k - c i)
        + (√(Qf c i j k) / Deltaf c i j k) •
            cross ((c j - c i) - (c k - c i)) (cross (c j - c i) (c k - c i)) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_triple_patch_moment
