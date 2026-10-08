import HardSphereB5Lean.Proofs.Proof_SolidGeom_triple_normal_form
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.triple_normal_form :
    ∀ (c : Fin 3 → E3)
    (hQ : 0 < 4 * dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2
        - (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 2) ^ 2 - dist (c 1) (c 2) ^ 2) ^ 2
        - dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2 * dist (c 1) (c 2) ^ 2), ∃ (o : E3) (e : Fin 3 → E3) (R ψ α₀ α₁ α₂ : ℝ), Orthonormal ℝ e ∧ 0 < R ∧ R < 1 ∧
      0 < α₀ ∧ 0 < α₁ ∧ 0 < α₂ ∧ α₀ + α₁ + α₂ = π ∧
      c 0 = o - R • (cos ψ • e 0 + sin ψ • e 1) ∧
      c 1 = o - R • (cos (ψ + 2 * α₂) • e 0 + sin (ψ + 2 * α₂) • e 1) ∧
      c 2 = o - R • (cos (ψ + 2 * α₂ + 2 * α₀) • e 0 + sin (ψ + 2 * α₂ + 2 * α₀) • e 1) :=
  @proof_SolidGeom_triple_normal_form
