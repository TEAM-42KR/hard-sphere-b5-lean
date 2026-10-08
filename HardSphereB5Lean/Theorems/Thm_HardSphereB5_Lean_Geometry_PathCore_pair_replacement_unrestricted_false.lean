import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_unrestricted_false
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.pair_replacement_unrestricted_false :
    ∃ x : Fin 3 → Pt, (∀ i j, i ≠ j → dist (x i) (x j) ^ 2 = 7 / 2) ∧
      QT (7 / 2) (7 / 2) (7 / 2) ≤ 0 ∧ (⋂ i, Metric.closedBall (x i) 1) = ∅ ∧
      0 < (volume (Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1)).toReal :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_unrestricted_false
