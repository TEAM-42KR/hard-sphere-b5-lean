import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_conditional
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.pair_replacement_conditional :
    ∀ (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
    (ha4 : dist (x 1) (x 2) ^ 2 < 4) (hb : dist (x 0) (x 1) ^ 2 ≤ 1) (hcc : dist (x 0) (x 2) ^ 2 ≤ 1)
    (hlong : dist (x 0) (x 1) ^ 2 ≤ dist (x 1) (x 2) ^ 2 ∧ dist (x 0) (x 2) ^ 2 ≤ dist (x 1) (x 2) ^ 2)
    (hQ : QT (dist (x 1) (x 2) ^ 2) (dist (x 1) (x 0) ^ 2) (dist (x 2) (x 0) ^ 2) ≤ 0), (volume (⋂ i, Metric.closedBall (x i) 1)).toReal = V2 (dist (x 1) (x 2)) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_conditional
