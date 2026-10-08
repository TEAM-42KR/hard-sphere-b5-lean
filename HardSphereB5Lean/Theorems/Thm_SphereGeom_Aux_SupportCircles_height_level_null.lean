import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_SupportCircles_height_level_null
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.Aux.SupportCircles.height_level_null :
    ∀ (n : E3) (hn : ‖n‖ = 1) (a : ℝ), dOmega {p | inner ℝ n p = a} = 0 :=
  @proof_SphereGeom_Aux_SupportCircles_height_level_null
