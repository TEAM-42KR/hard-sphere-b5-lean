import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem proof_SolidGeom_Q_positive_gram (x y z : E3)
 (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
 - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2) :
 0 < ‖y - x‖ ^ 2 * ‖z - x‖ ^ 2 - (inner ℝ (y - x) (z - x)) ^ 2 := by
  have hv : dist x y = ‖y - x‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hw : dist x z = ‖z - x‖ := by rw [dist_eq_norm, norm_sub_rev]
  have heq : y - z = (y - x) - (z - x) := by abel
  have hc : dist y z ^ 2 = ‖y - x‖ ^ 2 + ‖z - x‖ ^ 2 - 2 * inner ℝ (y - x) (z - x) := by
    rw [dist_eq_norm, heq, norm_sub_sq_real]
    ring
  rw [hv, hw] at hQ
  have hprod : 0 ≤ ‖y - x‖ ^ 2 * ‖z - x‖ ^ 2 * dist y z ^ 2 := by positivity
  nlinarith [hc]
