import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_radial_angle_prod_lintegral
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.radial_angle_prod_lintegral :
    ∀ (A B : ℝ), (∫⁻ q : ℝ × ℝ in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (q.1 ^ 2 * |A * Real.cos q.2 + B * Real.sin q.2|) ∂(volume.prod volume)) = ENNReal.ofReal ((4 / 3 : ℝ) * Real.sqrt (A ^ 2 + B ^ 2)) :=
  @proof_SphereGeom_Aux_Crofton_radial_angle_prod_lintegral
