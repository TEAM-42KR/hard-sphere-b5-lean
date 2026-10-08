import HardSphereB5Lean.Proofs.Proof_SphereGeom_pair_normalized_frame
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SphereGeom.pair_normalized_frame :
    ∀ (v w : E3)
 (hG : 0 < ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2), ∃ e : Fin 3 → E3, Orthonormal ℝ e ∧ v = ‖v‖ • e 0 ∧
 w = ‖w‖ • (Real.cos (Real.arccos (inner ℝ v w / (‖v‖ * ‖w‖))) • e 0 +
 Real.sin (Real.arccos (inner ℝ v w / (‖v‖ * ‖w‖))) • e 1) :=
  @proof_SphereGeom_pair_normalized_frame
