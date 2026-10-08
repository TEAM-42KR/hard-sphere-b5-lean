import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_angle_abs_integral
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.angle_abs_integral :
    ∀ (A B : ℝ), (∫ ψ in (0 : ℝ)..(2 * Real.pi), |A * Real.cos ψ + B * Real.sin ψ|) = 4 * Real.sqrt (A ^ 2 + B ^ 2) :=
  @proof_SphereGeom_Aux_Crofton_angle_abs_integral
