import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
noncomputable section
open SphereGeom
open scoped RealInnerProductSpace
theorem proof_CircleArc_ball_iff_inner (a k x : E3) (hx : x ∈ Metric.sphere a 1) :
    x ∈ Metric.closedBall k 1 ↔
      dist a k ^ 2 / 2 ≤ inner ℝ (x - a) (k - a) := by
  have hxa : ‖x - a‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  have hw : ‖k - a‖ = dist a k := by rw [← dist_eq_norm, dist_comm]
  have hvec : x - k = (x - a) - (k - a) := by abel
  have hsq : dist x k ^ 2 = 1 - 2 * inner ℝ (x - a) (k - a) + dist a k ^ 2 := by
    rw [dist_eq_norm, hvec, norm_sub_sq_real, hxa, hw]; norm_num
  rw [Metric.mem_closedBall]
  constructor
  · intro h
    nlinarith [dist_nonneg (x := x) (y := k)]
  · intro h
    nlinarith [dist_nonneg (x := x) (y := k)]
