import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_dOmega_compl_sphere : dOmega (Metric.sphere (0 : E3) 1)ᶜ = 0 := by
  rw [dOmega, sphereMeasure, Measure.map_apply (by fun_prop) (Metric.isClosed_sphere.measurableSet.compl)]
  have h : (fun u : Metric.sphere (0 : E3) 1 => (0 : E3) + (u : E3)) ⁻¹' (Metric.sphere (0 : E3) 1)ᶜ = ∅ := by
    ext u
    simp [u.property]
  rw [h, measure_empty]
