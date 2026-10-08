import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_gram_mixed
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SphereGeom.Aux.Santalo.gram_mixed :
    ∀ (nA nB u v : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1), (1 - inner ℝ u v ^ 2) *
        (inner ℝ nA v * inner ℝ nB u - inner ℝ nA nB * inner ℝ u v) +
      inner ℝ u v * inner ℝ nA (cross u v) * inner ℝ nB (cross u v) =
    (inner ℝ nA v - inner ℝ nA u * inner ℝ u v) *
      (inner ℝ nB u - inner ℝ nB v * inner ℝ u v) :=
  @proof_SphereGeom_Aux_Santalo_gram_mixed
