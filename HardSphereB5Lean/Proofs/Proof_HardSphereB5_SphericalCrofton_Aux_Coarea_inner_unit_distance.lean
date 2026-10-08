import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_inner_unit_distance (u v : Pt) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
  inner ℝ u v = 1 - dist u v ^ 2 / 2 := by
  have hn := norm_sub_sq_real u v
  rw [hu, hv] at hn
  rw [dist_eq_norm]
  linarith
