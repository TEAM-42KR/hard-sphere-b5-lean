import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_ConvexCone_line_frontier_unique
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

theorem SphereGeom.Aux.ConvexCone.line_frontier_unique :
    ∀ (C : Set SphereGeom.E3) (hclosed : IsClosed C) (hconvex : Convex ℝ C) (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ x ∈ C, r • x ∈ C) (v n w : SphereGeom.E3) (hv : v ∈ interior C) (hnv : 0 < inner ℝ n v) (hhalf : ∀ x ∈ C, 0 ≤ inner ℝ n x), ∃ s : ℝ, w + s • v ∈ frontier C ∧ ∀ t : ℝ, w + t • v ∈ frontier C → t = s :=
  @proof_SphereGeom_Aux_ConvexCone_line_frontier_unique
