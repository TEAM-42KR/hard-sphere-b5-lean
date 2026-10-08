import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_ConvexCone_positive_smul_transport
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

theorem SphereGeom.Aux.ConvexCone.positive_smul_transport :
    ∀ (C : Set SphereGeom.E3) (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ v ∈ C, r • v ∈ C) (r : ℝ) (hr : 0 < r) (x : SphereGeom.E3), (r • x ∈ interior C ↔ x ∈ interior C) ∧ (r • x ∈ frontier C ↔ x ∈ frontier C) :=
  @proof_SphereGeom_Aux_ConvexCone_positive_smul_transport
