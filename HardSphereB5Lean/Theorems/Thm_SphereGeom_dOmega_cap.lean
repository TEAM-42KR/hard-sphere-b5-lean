import HardSphereB5Lean.Proofs.Proof_SphereGeom_dOmega_cap
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.dOmega_cap :
    ∀ (n : E3) (hn : ‖n‖ = 1) (h : ℝ) (h1 : -1 ≤ h) (h2 : h ≤ 1), dOmega (cap n h) = ENNReal.ofReal (2 * Real.pi * (1 - h)) :=
  @proof_SphereGeom_dOmega_cap
