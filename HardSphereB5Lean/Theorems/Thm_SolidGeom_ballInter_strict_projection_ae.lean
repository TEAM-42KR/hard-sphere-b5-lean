import HardSphereB5Lean.Proofs.Proof_SolidGeom_ballInter_strict_projection_ae
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped BigOperators

theorem SolidGeom.ballInter_strict_projection_ae :
    ∀ (n : ℕ) (hn : 0 < n)
    (c : Fin n → E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e), ∀ᵐ p : ℝ × ℝ ∂volume,
      (∃ z : ℝ, p.1 • e 0 + p.2 • e 1 + z • e 2 ∈
        (⋂ i, Metric.closedBall (c i) 1)) →
      ∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
        (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1 :=
  @proof_SolidGeom_ballInter_strict_projection_ae
