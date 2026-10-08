import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_transverse_local_distance
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom Asymptotics Filter
open scoped Topology

theorem SphereGeom.Aux.Santalo.transverse_local_distance :
    ∀ (U V : ℝ → E3) (U' V' : E3) (a b : ℝ)
    (hU : HasDerivAt U U' a) (hV : HasDerivAt V V' b)
    (heq : U a = V b) (hcross : cross U' V' ≠ 0), ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ × ℝ in 𝓝 (a, b),
      c * ‖z - (a, b)‖ ≤ ‖U z.1 - V z.2‖ :=
  @proof_SphereGeom_Aux_Santalo_transverse_local_distance
