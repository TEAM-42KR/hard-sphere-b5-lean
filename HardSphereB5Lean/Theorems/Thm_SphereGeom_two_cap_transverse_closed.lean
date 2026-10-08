import HardSphereB5Lean.Proofs.Proof_SphereGeom_two_cap_transverse_closed
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.two_cap_transverse_closed :
    ∀ (A K L : ℝ) (hA0 : 0 < A) (hA2 : A < 2) (hL : 0 < L) (hB2 : K ^ 2 + L ^ 2 < 4) (hH : 0 < L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2),
    let B := Real.sqrt (K ^ 2 + L ^ 2); let H := L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2; (2 / L) * (∫ t in (A / 2)..1, Real.sqrt (L ^ 2 * (1 - t ^ 2) - ((K ^ 2 + L ^ 2) / 2 - K * t) ^ 2)) = ((1 - B ^ 2 / 4) * L / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ - Real.sqrt H * (A - K) / (2 * L) :=
  @proof_SphereGeom_two_cap_transverse_closed
