import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_swap (u v τ1 τ2 : Pt) : santaloDens u v τ1 τ2 = santaloDens v u τ2 τ1 := by
  have hc : cross v u = -(cross u v) := by
    ext i
    fin_cases i <;> simp [cross, cross_apply] <;> ring
  unfold santaloDens
  rw [hc, inner_neg_left, inner_neg_left, abs_neg, abs_neg, real_inner_comm v u]
  rw [mul_comm]
