import HardSphereB5Lean.Proofs.Proof_SolidGeom_ae_ballInter_slice_endpoint_unique
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.ae_ballInter_slice_endpoint_unique :
    ∀ (n : ℕ) (c : Fin n → E3)
    (hc : Function.Injective c) (e : Fin 3 → E3) (he : Orthonormal ℝ e),
    let D : Set (ℝ × ℝ) := {p | ∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
      (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ D →
      (∀ i j, l i p = l j p → i = j) ∧ (∀ i j, u i p = u j p → i = j) :=
  @proof_SolidGeom_ae_ballInter_slice_endpoint_unique
