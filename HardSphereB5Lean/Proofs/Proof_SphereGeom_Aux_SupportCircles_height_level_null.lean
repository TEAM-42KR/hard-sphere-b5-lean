import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false
open MeasureTheory Real SphereGeom
noncomputable section

theorem proof_SphereGeom_Aux_SupportCircles_height_level_null (n : E3) (hn : ‖n‖ = 1) (a : ℝ) : dOmega {p | inner ℝ n p = a} = 0 := by
  have hh : dOmega.map (fun p : E3 => inner ℝ n p) {a} = 0 := by
    rw [SphereGeom.dOmega_map_inner n hn]
    simp
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton a)] at hh
  have heq : (fun p : E3 => inner ℝ n p) ⁻¹' ({a} : Set ℝ) = {p : E3 | inner ℝ n p = a} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [heq] at hh
  exact hh

