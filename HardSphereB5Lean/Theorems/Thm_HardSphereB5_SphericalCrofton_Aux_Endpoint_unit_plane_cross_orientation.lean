import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_unit_plane_cross_orientation
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.unit_plane_cross_orientation :
    ∀ (u v p : Pt) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1) (hne : u ≠ v) (hanti : u ≠ -v) (hpu : inner ℝ p u = 0) (hpv : inner ℝ p v = 0), cross u v ≠ 0 ∧ ((unitDir (cross u v) = p ∧ unitDir (cross v u) = -p) ∨ (unitDir (cross u v) = -p ∧ unitDir (cross v u) = p)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_unit_plane_cross_orientation
