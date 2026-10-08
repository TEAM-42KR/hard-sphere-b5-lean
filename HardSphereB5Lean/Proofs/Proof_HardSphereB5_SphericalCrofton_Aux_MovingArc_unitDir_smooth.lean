import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_unitDir_smooth (x : Pt) (hx : x ≠ 0) : ContDiffAt ℝ ⊤ unitDir x := by
  unfold unitDir
  exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
