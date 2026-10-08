import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_positive_volume_active_patches
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.positive_volume_active_patches :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), 0 < vol c Finset.univ ∧ (∀ i, 0 < pArea c i Finset.univ) ∧
      ∀ i, Nonempty (patch c i ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_positive_volume_active_patches
