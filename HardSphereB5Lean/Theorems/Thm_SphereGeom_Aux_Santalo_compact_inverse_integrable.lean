import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Santalo_compact_inverse_integrable
import Mathlib
set_option autoImplicit false
open MeasureTheory Asymptotics Filter
open scoped Topology

theorem SphereGeom.Aux.Santalo.compact_inverse_integrable :
    ∀ (S : (ℝ × ℝ) → ℝ) (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hS : Continuous S) (hnonneg : ∀ z ∈ K, 0 ≤ S z)
    (hlocal : ∀ p ∈ K, S p = 0 → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ z in 𝓝[K] p, c * ‖z - p‖ ≤ S z), IntegrableOn (fun z => (S z)⁻¹) K volume :=
  @proof_SphereGeom_Aux_Santalo_compact_inverse_integrable
