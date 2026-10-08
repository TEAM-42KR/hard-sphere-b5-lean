import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Arrangement_remove_finite_residual
import Mathlib
set_option autoImplicit false

theorem SphereGeom.Aux.Arrangement.remove_finite_residual :
    ∀ (X : Type*) [MetricSpace X] (A F B : Set X) (hA : IsClosed A) (hF : F.Finite) (hB : B = A ∪ F) (hacc : ∀ u ∈ B, ∀ ε : ℝ, 0 < ε → ∃ v ∈ B, v ≠ u ∧ dist v u < ε), B = A :=
  @proof_SphereGeom_Aux_Arrangement_remove_finite_residual
