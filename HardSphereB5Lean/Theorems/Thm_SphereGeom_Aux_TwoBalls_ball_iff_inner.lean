import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_TwoBalls_ball_iff_inner
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom MeasureTheory

theorem SphereGeom.Aux.TwoBalls.ball_iff_inner :
    ∀ (D E u : E3) (hu : ‖u‖ = 1), (‖D + u‖ ≤ 1 ∧ ‖D + u - E‖ ≤ 1) ↔ (‖D‖ ^ 2 + 2 * inner ℝ D u ≤ 0 ∧ ‖D - E‖ ^ 2 + 2 * inner ℝ (D - E) u ≤ 0) :=
  @proof_SphereGeom_Aux_TwoBalls_ball_iff_inner
