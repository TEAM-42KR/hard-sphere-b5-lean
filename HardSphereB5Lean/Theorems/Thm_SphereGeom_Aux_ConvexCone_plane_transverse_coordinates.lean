import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_ConvexCone_plane_transverse_coordinates
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

theorem SphereGeom.Aux.ConvexCone.plane_transverse_coordinates :
    ∀ (p v : SphereGeom.E3) (hp : ‖p‖ = 1) (hv : v ≠ 0) (hpv : inner ℝ p v = 0), ∃ w : SphereGeom.E3, inner ℝ p w = 0 ∧ LinearIndependent ℝ ![v,w] ∧ ∀ x : SphereGeom.E3, inner ℝ p x = 0 → ∃ s t : ℝ, x = s • v + t • w :=
  @proof_SphereGeom_Aux_ConvexCone_plane_transverse_coordinates
