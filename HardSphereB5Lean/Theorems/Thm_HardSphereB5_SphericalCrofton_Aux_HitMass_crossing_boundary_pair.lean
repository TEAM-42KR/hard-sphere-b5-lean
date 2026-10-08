import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_crossing_boundary_pair
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.crossing_boundary_pair :
    ∀ {K : Set Pt}
    (hK : IsRegularRegionCrofton K) (p : Pt) (hp : ‖p‖ = 1)
    (hneg : ∃ u ∈ K, inner ℝ p u < 0) (hpos : ∃ u ∈ K, 0 < inner ℝ p u), ∃ a b : Pt, a ≠ b ∧ greatCircle p ∩ sFrontier K = {a, b} ∧
      0 < chordLen K (greatCircle p) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_crossing_boundary_pair
