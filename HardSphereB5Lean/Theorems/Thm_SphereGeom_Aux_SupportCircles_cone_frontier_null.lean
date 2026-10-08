import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_SupportCircles_cone_frontier_null
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.Aux.SupportCircles.cone_frontier_null :
    ∀ (C : Set E3) (hC : Convex ℝ C) (hcone : ∀ r : ℝ, 0 < r → (fun x : E3 => r • x) ⁻¹' C = C), dOmega (frontier C) = 0 :=
  @proof_SphereGeom_Aux_SupportCircles_cone_frontier_null
