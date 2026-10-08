import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom MeasureTheory

noncomputable section

theorem proof_SphereGeom_Aux_SurfaceArea_interior_pos (A : Set E3) (hA : MeasurableSet A)
    (hi : (interior ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ⁻¹' A)).Nonempty) :
    0 < (dOmega A).toReal := by
  unfold dOmega sphereMeasure
  rw [Measure.map_apply (by fun_prop) hA]
  have hp : 0 < (volume : Measure E3).toSphere
      ((fun u : Metric.sphere (0 : E3) 1 => (0 : E3) + (u : E3)) ⁻¹' A) := by
    simpa only [zero_add] using
      (lt_of_lt_of_le
        (isOpen_interior.measure_pos (μ := (volume : Measure E3).toSphere) hi)
        (measure_mono interior_subset))
  exact ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
