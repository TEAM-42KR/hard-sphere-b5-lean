import HardSphereB5Lean.Proofs.Proof_SphereGeom_lintegral_pair_greatCircle
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.lintegral_pair_greatCircle :
    ∀ (F₁ F₂ : E3 → E3) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hF : ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p]) (g : E3 → E3 → ENNReal)
    (hg : Measurable (Function.uncurry g)), ∫⁻ u, ∫⁻ v, g u v ∂dOmega ∂dOmega =
      (1 / 2 : ENNReal) * ∫⁻ p, ∫⁻ t₁ in Set.Ioc 0 (2 * Real.pi), ∫⁻ t₂ in Set.Ioc 0 (2 * Real.pi),
        g (Real.cos t₁ • F₁ p + Real.sin t₁ • F₂ p) (Real.cos t₂ • F₁ p + Real.sin t₂ • F₂ p) *
          ENNReal.ofReal |Real.sin (t₁ - t₂)| ∂volume ∂volume ∂dOmega :=
  @proof_SphereGeom_lintegral_pair_greatCircle
