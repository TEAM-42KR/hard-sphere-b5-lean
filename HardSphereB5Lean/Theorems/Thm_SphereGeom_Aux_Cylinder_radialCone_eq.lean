import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Cylinder_radialCone_eq
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem SphereGeom.Aux.Cylinder.radialCone_eq :
    ∀ (A : Set E3), Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ''
      {u : Metric.sphere (0 : E3) 1 | (u : E3) ∈ A}) =
      {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ (‖x‖⁻¹ : ℝ) • x ∈ A} :=
  @proof_SphereGeom_Aux_Cylinder_radialCone_eq
