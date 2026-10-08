import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_no_sliver_at_s_one {X : ℝ} {Y : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) :
    0 < P4poly X Y 1 := by
  have h : P4poly X Y 1 = X * Y * (5 + 3 * (1 - X) + 3 * (1 - Y) + (1 - X) * (1 - Y)) := by
    unfold P4poly; ring
  have h1 : 0 < 1 - X := by linarith
  have h2 : 0 < 1 - Y := by linarith
  have h3 : 0 < 5 + 3 * (1 - X) + 3 * (1 - Y) + (1 - X) * (1 - Y) := by
    nlinarith [mul_pos h1 h2]
  rw [h]
  exact mul_pos (mul_pos hX hY) h3

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_no_sliver_at_s_one
