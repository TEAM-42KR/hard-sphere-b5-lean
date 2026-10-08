import HardSphereB5Lean.Proofs.Proof_SolidGeom_Q_positive_parameters
import Mathlib
set_option autoImplicit false

theorem SolidGeom.Q_positive_parameters :
    ∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
 (hQ : 0 < 4 * a * b - (a + b - c) ^ 2 - a * b * c), 0 < a ∧ a < 4 ∧ 0 < b ∧ b < 4 ∧ 0 < c ∧ c < 4 ∧
  0 < 4 * a * b - (a + b - c) ^ 2 :=
  @proof_SolidGeom_Q_positive_parameters
