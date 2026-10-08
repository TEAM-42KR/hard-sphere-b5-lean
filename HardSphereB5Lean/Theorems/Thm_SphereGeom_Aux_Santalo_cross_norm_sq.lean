import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_cross_norm_sq
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SphereGeom.Aux.Santalo.cross_norm_sq :
    ∀ (u v : E3), ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 :=
  @proof_SphereGeom_Aux_Santalo_cross_norm_sq
