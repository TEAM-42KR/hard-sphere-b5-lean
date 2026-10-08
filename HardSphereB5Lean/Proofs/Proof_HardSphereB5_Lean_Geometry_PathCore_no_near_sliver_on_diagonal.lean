import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_H_diagonal (Y s : ℝ) :
    Hpoly Y Y s = (s-(1-Y)^2)*(1+2*Y-s) := by unfold Hpoly; ring
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_P4_diagonal (Y s : ℝ) :
    P4poly Y Y s = (s-(1-Y)^2)*(Y*(6-Y)+3*(1-s)) := by unfold P4poly; ring
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_no_near_sliver_on_diagonal_of_deps {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hs : s < 1) (hXY : X = Y) : 0 < P4poly X Y s := by
  subst X
  have hH := hc.H_pos
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_H_diagonal] at hH
  have hw : 0 < s-(1-Y)^2 := by
    have hh : 0 < 1+2*Y-s := by linarith [hc.Y_pos]
    exact (mul_pos_iff_of_pos_right hh).mp hH
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_P4_diagonal]
  apply mul_pos hw
  have hq : 0 < Y*(6-Y) := mul_pos hc.Y_pos (by linarith [hc.Y_lt_one])
  linarith
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_no_near_sliver_on_diagonal {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs : s < 1) (hXY : X = Y) :
    0 < P4poly X Y s := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_no_near_sliver_on_diagonal_of_deps c X Y s hc hs hXY

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_no_near_sliver_on_diagonal
