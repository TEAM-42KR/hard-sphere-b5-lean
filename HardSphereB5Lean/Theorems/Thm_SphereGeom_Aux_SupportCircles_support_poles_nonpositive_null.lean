import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_SupportCircles_support_poles_nonpositive_null
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SupportCircles_cone_frontier_null
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.Aux.SupportCircles.support_poles_nonpositive_null :
    ∀ (K : Set E3) (hK : K ⊆ Metric.sphere (0 : E3) 1), dOmega {p : E3 | ‖p‖ = 1 ∧ (∀ u ∈ K, inner ℝ p u ≤ 0) ∧ ∃ u ∈ K, inner ℝ p u = 0} = 0 :=
  @proof_SphereGeom_Aux_SupportCircles_support_poles_nonpositive_null
