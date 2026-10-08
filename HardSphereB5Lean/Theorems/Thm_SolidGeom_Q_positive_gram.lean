import HardSphereB5Lean.Proofs.Proof_SolidGeom_Q_positive_gram
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SolidGeom.Q_positive_gram :
    ∀ (x y z : E3)
 (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
 - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2), 0 < ‖y - x‖ ^ 2 * ‖z - x‖ ^ 2 - (inner ℝ (y - x) (z - x)) ^ 2 :=
  @proof_SolidGeom_Q_positive_gram
