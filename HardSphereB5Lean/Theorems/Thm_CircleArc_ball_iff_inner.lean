import HardSphereB5Lean.Proofs.Proof_CircleArc_ball_iff_inner
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
open scoped RealInnerProductSpace

theorem CircleArc.ball_iff_inner :
    ∀ (a k x : E3) (hx : x ∈ Metric.sphere a 1), x ∈ Metric.closedBall k 1 ↔
      dist a k ^ 2 / 2 ≤ inner ℝ (x - a) (k - a) :=
  @proof_CircleArc_ball_iff_inner
