import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_dOmega_greatCircle_eq_zero (n : E3) (hn : ‖n‖ = 1) : dOmega (greatCircle n) = 0 := by
  have hm : Measurable (fun u : E3 => inner ℝ n u) :=
    (continuous_const.inner continuous_id).measurable
  have hz : dOmega ((fun u : E3 => inner ℝ n u) ⁻¹' ({0} : Set ℝ)) = 0 := by
    rw [← Measure.map_apply hm (measurableSet_singleton 0), dOmega_map_inner n hn]
    simp
  exact measure_mono_null (fun x hx => hx.2) hz
