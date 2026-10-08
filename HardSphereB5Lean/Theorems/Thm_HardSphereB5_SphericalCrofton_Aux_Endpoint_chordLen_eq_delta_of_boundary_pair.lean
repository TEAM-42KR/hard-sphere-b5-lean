import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_chordLen_eq_delta_of_boundary_pair
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.chordLen_eq_delta_of_boundary_pair :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (p u v : Pt) (hp : ‖p‖ = 1) (huv : u ≠ v) (hb : greatCircle p ∩ sFrontier K = {u,v}) (hpos : 0 < chordLen K (greatCircle p)), 0 < arccos (inner ℝ u v) ∧ chordLen K (greatCircle p) = arccos (inner ℝ u v) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_chordLen_eq_delta_of_boundary_pair
