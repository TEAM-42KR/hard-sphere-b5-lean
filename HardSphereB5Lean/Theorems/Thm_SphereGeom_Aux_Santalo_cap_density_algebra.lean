import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_cap_density_algebra
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open scoped Classical

theorem SphereGeom.Aux.Santalo.cap_density_algebra :
    ∀ (nA nB u v : E3) (a b : ℝ)
    (hnA : ‖nA‖ = 1) (hnB : ‖nB‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hAu : inner ℝ nA u = a) (hBv : inner ℝ nB v = b)
    (hAv : a ≤ inner ℝ nA v) (hBu : b ≤ inner ℝ nB u)
    (hx0 : -1 < inner ℝ u v) (hx1 : inner ℝ u v < 1), ‖cross nA u‖ = Real.sqrt (1 - a ^ 2) ∧
    ‖cross nB v‖ = Real.sqrt (1 - b ^ 2) ∧
    0 ≤ inner ℝ nA v - a * inner ℝ u v ∧
    0 ≤ inner ℝ nB u - b * inner ℝ u v ∧
    Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) *
      santaloDens u v (unitDir (cross nA u)) (unitDir (cross nB v)) =
      (inner ℝ nA v - a * inner ℝ u v) *
        (inner ℝ nB u - b * inner ℝ u v) /
          Real.sin (Real.arccos (inner ℝ u v)) ^ 3 :=
  @proof_SphereGeom_Aux_Santalo_cap_density_algebra
