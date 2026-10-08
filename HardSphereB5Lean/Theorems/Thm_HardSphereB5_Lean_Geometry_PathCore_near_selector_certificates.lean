import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_certificates
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.near_selector_certificates :
    ∀ (X Y s t : ℝ), P4poly X Y s = -Y*(4-Y)*X^2+2*Y*(s+5-2*Y)*X-3*(s-1)^2 ∧
  Y^2*(s+5-2*Y)^2-3*Y*(4-Y)*(s-1)^2=4*Y*(3-Y)*Qpoly X Y s 1 ∧
  Hpoly Y Y s = (s-s0 Y)*(1+2*Y-s) ∧
  P4poly Y Y (1-t) = (Y*(2-Y)-t)*(Y*(6-Y)+3*t) ∧
  P4poly 1 Y (1-t) = Y*(1-Y)^2*(8-3*Y)+(Y*(2-Y)-t)*(3*(Y*(2-Y)+t)+2*Y) ∧
  Hpoly X Y (s0 Y) = -Y*(X-Y)*(X-(2-Y)^2) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_certificates
