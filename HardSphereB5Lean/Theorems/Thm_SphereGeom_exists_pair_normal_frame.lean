import HardSphereB5Lean.Proofs.Proof_SphereGeom_exists_pair_normal_frame
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SphereGeom.exists_pair_normal_frame :
    ∀ (v w : E3)
  (hG : 0 < ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2), ∃ e : Fin 3 → E3, Orthonormal ℝ e ∧
    v = ‖v‖ • e 0 ∧
    w = (inner ℝ v w / ‖v‖) • e 0 +
      Real.sqrt (‖w‖ ^ 2 - (inner ℝ v w / ‖v‖) ^ 2) • e 1 :=
  @proof_SphereGeom_exists_pair_normal_frame
