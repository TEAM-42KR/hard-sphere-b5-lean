import HardSphereB5Lean.Proofs.Proof_SolidGeom_integral_max_cos_sectors
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.integral_max_cos_sectors :
    ∀ (F : ℝ → ℝ) (hF : Continuous F) (ψ α₀ α₁ α₂ : ℝ) (h0 : 0 < α₀)
    (h1 : 0 < α₁) (h2 : 0 < α₂) (hs : α₀ + α₁ + α₂ = π), ∫ φ in ψ..ψ + 2 * π,
        F (max (cos (φ - ψ)) (max (cos (φ - (ψ + 2 * α₂))) (cos (φ - (ψ + 2 * α₂ + 2 * α₀))))) =
      2 * ((∫ t in (0 : ℝ)..α₀, F (cos t)) + (∫ t in (0 : ℝ)..α₁, F (cos t)) +
        ∫ t in (0 : ℝ)..α₂, F (cos t)) :=
  @proof_SolidGeom_integral_max_cos_sectors
