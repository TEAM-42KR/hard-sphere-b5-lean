import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_rational_remainder_bound
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SphereGeom.Aux.Santalo.rational_remainder_bound :
    ∀ (nA nB u v : E3) (q : ℝ) (hnA : ‖nA‖ ≤ 1) (hnB : ‖nB‖ ≤ 1)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1), |q / (1 - inner ℝ u v ^ 2) * inner ℝ nA (cross u v) * inner ℝ nB (cross u v)|
      ≤ |q| :=
  @proof_SphereGeom_Aux_Santalo_rational_remainder_bound
