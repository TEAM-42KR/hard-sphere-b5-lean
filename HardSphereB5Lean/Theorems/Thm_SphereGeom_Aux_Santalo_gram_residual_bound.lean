import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_gram_residual_bound
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SphereGeom.Aux.Santalo.gram_residual_bound :
    ∀ (n u v : E3) (hn : ‖n‖ ≤ 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1), |inner ℝ n v - inner ℝ n u * inner ℝ u v| ≤ Real.sqrt (1 - inner ℝ u v ^ 2) :=
  @proof_SphereGeom_Aux_Santalo_gram_residual_bound
