import HardSphereB5Lean.Proofs.Proof_SolidGeom_volume_normal_form_angular
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.volume_normal_form_angular :
    ∀ (c : Fin 3 → E3) (o : E3) (e : Fin 3 → E3) (R ψ α₀ α₁ α₂ : ℝ)
    (he : Orthonormal ℝ e) (hR0 : 0 < R) (hR1 : R < 1)
    (h0 : 0 < α₀) (h1 : 0 < α₁) (h2 : 0 < α₂) (hs : α₀ + α₁ + α₂ = π)
    (hc0 : c 0 = o - R • (cos ψ • e 0 + sin ψ • e 1))
    (hc1 : c 1 = o - R • (cos (ψ + 2 * α₂) • e 0 + sin (ψ + 2 * α₂) • e 1))
    (hc2 : c 2 = o - R • (cos (ψ + 2 * α₂ + 2 * α₀) • e 0 +
      sin (ψ + 2 * α₂ + 2 * α₀) • e 1)),
    let h := √(1 - R ^ 2)
    let I : ℝ → ℝ := fun p => 2 / 3 * h ^ 3 + p ^ 2 * h
      - p * (h ^ 2 + p ^ 2) * (π / 2 - arctan (p / h))
    (volume (Metric.closedBall (c 0) 1 ∩ Metric.closedBall (c 1) 1 ∩
      Metric.closedBall (c 2) 1)).toReal =
      ∫ φ in ψ..ψ + 2 * π,
        I (R * max (cos (φ - ψ)) (max (cos (φ - (ψ + 2 * α₂)))
          (cos (φ - (ψ + 2 * α₂ + 2 * α₀))))) :=
  @proof_SolidGeom_volume_normal_form_angular
