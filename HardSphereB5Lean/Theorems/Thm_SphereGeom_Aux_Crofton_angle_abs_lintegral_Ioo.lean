import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_angle_abs_lintegral_Ioo
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.angle_abs_lintegral_Ioo :
    ∀ (A B : ℝ), (∫⁻ ψ in Set.Ioo (0 : ℝ) (2 * Real.pi), ENNReal.ofReal |A * Real.cos ψ + B * Real.sin ψ|) = ENNReal.ofReal (4 * Real.sqrt (A ^ 2 + B ^ 2)) :=
  @proof_SphereGeom_Aux_Crofton_angle_abs_lintegral_Ioo
