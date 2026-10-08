import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_ConvexCone_plane_boundary_pair
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

theorem SphereGeom.Aux.ConvexCone.plane_boundary_pair :
    ∀ (C : Set SphereGeom.E3) (hclosed : IsClosed C) (hconvex : Convex ℝ C) (hzero : (0 : SphereGeom.E3) ∈ C) (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ v ∈ C, r • v ∈ C) (p : SphereGeom.E3) (hp : ‖p‖ = 1) (hinter : ∃ v ∈ interior C, inner ℝ p v = 0) (hhalf : ∃ n : SphereGeom.E3, n ≠ 0 ∧ ∀ v ∈ C, 0 ≤ inner ℝ n v), ∃ a b : SphereGeom.E3, a ≠ b ∧ SphereGeom.greatCircle p ∩ frontier C = {a,b} :=
  @proof_SphereGeom_Aux_ConvexCone_plane_boundary_pair
