import HardSphereB5Lean.Proofs.Proof_SolidGeom_ballInter_slice_partition_ae
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.ballInter_slice_partition_ae :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → E3)
    (hc : Function.Injective c) (e : Fin 3 → E3) (he : Orthonormal ℝ e),
    let D : Set (ℝ × ℝ) := {p | ∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
      (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ D → ∃ i j,
      (∀ k, l k p ≤ l i p ∧ u j p ≤ u k p) ∧
      (∀ z : ℝ, p.1 • e 0 + p.2 • e 1 + z • e 2 ∈
        (⋂ k, Metric.closedBall (c k) 1) ↔ z ∈ Set.Icc (l i p) (u j p)) ∧
      (∀ F : ℝ → ℝ,
        (∑ k, if u k p ∈ Set.Icc (l i p) (u j p) then F (u k p) else 0) -
          (∑ k, if l k p ∈ Set.Icc (l i p) (u j p) then F (l k p) else 0) =
            if l i p ≤ u j p then F (u j p) - F (l i p) else 0) :=
  @proof_SolidGeom_ballInter_slice_partition_ae
