import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem proof_SphereGeom_cross_vec_triple (u v w : E3) :
    cross u (cross v w) = (inner ℝ u w) • v - (inner ℝ v u) • w := by
  ext i
  fin_cases i <;>
    simp [SphereGeom.cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three] <;>
    ring
