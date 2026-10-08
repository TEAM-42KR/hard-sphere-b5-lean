import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_ae_radial_of_ae_spherical (P : Pt → Prop) (hP : ∀ᵐ p ∂dOmega, P p) :
    ∀ᵐ y ∂((volume : Measure Pt).restrict (Metric.ball (0:Pt) 1)), P (‖y‖⁻¹ • y) := by
  have hN : Measurable (fun y : Pt => ‖y‖⁻¹ • y) := by fun_prop
  rw [SphereGeom.Aux.Crofton.dOmega_eq_three_smul_map_radial] at hP
  have hm : ∀ᵐ p ∂((volume : Measure Pt).restrict (Metric.ball (0:Pt) 1)).map
      (fun y : Pt => ‖y‖⁻¹ • y), P p := by
    exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (3:ENNReal) ≠ 0)).mp hP
  exact ae_of_ae_map hN.aemeasurable hm
