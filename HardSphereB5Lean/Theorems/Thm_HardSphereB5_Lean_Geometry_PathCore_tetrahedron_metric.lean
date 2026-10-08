import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.tetrahedron_metric :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), 0 < s ∧ s < 3 ∧ AffineIndependent ℝ c ∧
  (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < Deltaf c i j k) ∧
  (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)) ^ 2 = Hpoly X Y s / 4 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric
