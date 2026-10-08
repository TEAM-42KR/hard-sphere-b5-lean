import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_certificates (X Y s t : ℝ) :
  P4poly X Y s = -Y*(4-Y)*X^2+2*Y*(s+5-2*Y)*X-3*(s-1)^2 ∧
  Y^2*(s+5-2*Y)^2-3*Y*(4-Y)*(s-1)^2=4*Y*(3-Y)*Qpoly X Y s 1 ∧
  Hpoly Y Y s = (s-s0 Y)*(1+2*Y-s) ∧
  P4poly Y Y (1-t) = (Y*(2-Y)-t)*(Y*(6-Y)+3*t) ∧
  P4poly 1 Y (1-t) = Y*(1-Y)^2*(8-3*Y)+(Y*(2-Y)-t)*(3*(Y*(2-Y)+t)+2*Y) ∧
  Hpoly X Y (s0 Y) = -Y*(X-Y)*(X-(2-Y)^2) := by
  repeat' constructor
  all_goals simp only [P4poly, Hpoly, Qpoly, s0, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  all_goals ring

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_certificates
