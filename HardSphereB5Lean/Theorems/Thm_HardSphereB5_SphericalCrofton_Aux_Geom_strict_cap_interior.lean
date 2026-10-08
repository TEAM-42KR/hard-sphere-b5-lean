import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_strict_cap_interior
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.strict_cap_interior :
    ∀ (x y u : Pt) (a b : ℝ)
    (hu : ‖u‖ = 1) (hx : a < inner ℝ x u) (hy : b < inner ℝ y u), u ∈ sInterior {v : Pt | ‖v‖ = 1 ∧ a ≤ inner ℝ x v ∧ b ≤ inner ℝ y v} :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_strict_cap_interior
