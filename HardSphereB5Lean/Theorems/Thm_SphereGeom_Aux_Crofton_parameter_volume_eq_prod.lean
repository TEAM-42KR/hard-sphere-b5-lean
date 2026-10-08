import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_parameter_volume_eq_prod
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.parameter_volume_eq_prod :
    ∀ (S T U : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U) (F : ℝ × (ℝ × ℝ) → ENNReal) (hF : Measurable F), (∫⁻ x : E3 in {x | x 0 ∈ S ∧ x 1 ∈ T ∧ x 2 ∈ U}, F (x 0, (x 1, x 2))) = ∫⁻ p : ℝ × (ℝ × ℝ) in S ×ˢ (T ×ˢ U), F p ∂(volume.prod (volume.prod volume)) :=
  @proof_SphereGeom_Aux_Crofton_parameter_volume_eq_prod
