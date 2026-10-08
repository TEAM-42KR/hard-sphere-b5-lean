import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_transverse_ae
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.pair_transverse_ae :
    ∀ (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)), ∀ᵐ q ∂weightedPairMu D, ‖pairPole q‖ = 1 ∧ q.1 ≠ q.2 ∧
      q.1 ∈ greatCircle (pairPole q) ∩ sFrontier (SigmaD D) ∧
      q.2 ∈ greatCircle (pairPole q) ∩ sFrontier (SigmaD D) ∧
      (∃ u ∈ SigmaD D, inner ℝ (pairPole q) u < 0) ∧
      (∃ v ∈ SigmaD D, 0 < inner ℝ (pairPole q) v) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_transverse_ae
