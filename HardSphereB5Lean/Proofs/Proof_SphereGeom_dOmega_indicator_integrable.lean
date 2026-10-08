import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_dOmega_indicator_integrable (A : Set E3) (hA : MeasurableSet A) :
 Integrable (A.indicator (fun _ : E3 => (1 : ℝ))) dOmega := by
  letI : IsFiniteMeasure dOmega := by
    unfold dOmega sphereMeasure
    infer_instance
  exact (integrable_const (1 : ℝ)).indicator hA
