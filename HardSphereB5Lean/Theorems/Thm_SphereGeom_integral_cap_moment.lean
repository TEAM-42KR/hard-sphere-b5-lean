import HardSphereB5Lean.Proofs.Proof_SphereGeom_integral_cap_moment
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.integral_cap_moment :
    ∀ (n : E3) (hn : ‖n‖ = 1) (h : ℝ) (h1 : -1 ≤ h) (h2 : h ≤ 1), ∫ u in cap n h, u ∂dOmega = (Real.pi * (1 - h ^ 2)) • n :=
  @proof_SphereGeom_integral_cap_moment
