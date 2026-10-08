import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom MeasureTheory

noncomputable section

theorem proof_SphereGeom_Aux_TwoBalls_ball_iff_inner (D E u : E3) (hu : ‖u‖ = 1) :
    (‖D + u‖ ≤ 1 ∧ ‖D + u - E‖ ≤ 1) ↔
      (‖D‖ ^ 2 + 2 * inner ℝ D u ≤ 0 ∧
       ‖D - E‖ ^ 2 + 2 * inner ℝ (D - E) u ≤ 0) := by
  have aux (v : E3) : ‖v + u‖ ≤ 1 ↔ ‖v‖ ^ 2 + 2 * inner ℝ v u ≤ 0 := by
    have hh := norm_add_sq_real v u
    rw [hu] at hh
    constructor
    · intro hv
      nlinarith [norm_nonneg (v + u)]
    · intro hv
      nlinarith [norm_nonneg (v + u)]
  have heq : D + u - E = (D - E) + u := by abel
  rw [heq, aux D, aux (D - E)]
