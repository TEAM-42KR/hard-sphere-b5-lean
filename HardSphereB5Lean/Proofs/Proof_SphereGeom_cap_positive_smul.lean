import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem proof_SphereGeom_cap_positive_smul (n : E3) (h d : ℝ) (hd : 0 < d) :
 cap (d • n) (d * h) = cap n h := by
  ext u
  simp only [cap, Set.mem_setOf_eq, real_inner_smul_left, mul_le_mul_iff_right₀ hd]
