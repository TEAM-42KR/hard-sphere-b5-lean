import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_convex_crossing_interior
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.convex_crossing_interior :
    ∀ (C : Set Pt) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (hint : (interior C).Nonempty) (p : Pt)
    (hneg : ∃ u ∈ C, inner ℝ p u < 0) (hpos : ∃ u ∈ C, 0 < inner ℝ p u), ∃ v ∈ interior C, inner ℝ p v = 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_convex_crossing_interior
