import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Cylinder_norm_chart
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Cylinder.norm_chart :
    ∀ (r z phi : ℝ) (hz : -1 ≤ z ∧ z ≤ 1), ‖(WithLp.toLp 2 ![r * Real.sqrt (1-z^2) * Real.cos phi,
      r * Real.sqrt (1-z^2) * Real.sin phi, r*z] : E3)‖ = |r| :=
  @proof_SphereGeom_Aux_Cylinder_norm_chart
