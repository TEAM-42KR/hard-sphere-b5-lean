import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_triple_patch_moment_scalar
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.triple_patch_moment_scalar :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (cs : Pt), inner ℝ (cs - c i) (pMoment c i {i, j, k}) =
      (1 - q c i j / 4) * inner ℝ (cs - c i) (c j - c i) * betaA c i j k / √(q c i j)
        + (1 - q c i k / 4) * inner ℝ (cs - c i) (c k - c i) * betaA c i k j / √(q c i k)
        + √(Qf c i j k) * ((q c i j - q c i k - q c j k) * inner ℝ (cs - c i) (c j - c i)
            - (q c i j - q c i k + q c j k) * inner ℝ (cs - c i) (c k - c i)) /
          (2 * Deltaf c i j k) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_triple_patch_moment_scalar
