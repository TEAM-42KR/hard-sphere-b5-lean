import HardSphereB5Lean.Proofs.Proof_SphereGeom_incidence_swap
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.incidence_swap :
    ∀ (F₁ F₂ : E3 → E3) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hF : ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p]) (H : E3 → E3 → ENNReal)
    (hH : Measurable (Function.uncurry H)), ∫⁻ p, (∫⁻ t in Set.Ioc 0 (2 * Real.pi), H p (Real.cos t • F₁ p + Real.sin t • F₂ p)) ∂dOmega =
      ∫⁻ u, (∫⁻ t in Set.Ioc 0 (2 * Real.pi), H (Real.cos t • F₁ u + Real.sin t • F₂ u) u) ∂dOmega :=
  @proof_SphereGeom_incidence_swap
