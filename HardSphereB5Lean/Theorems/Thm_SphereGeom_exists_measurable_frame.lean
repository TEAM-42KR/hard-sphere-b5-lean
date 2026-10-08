import HardSphereB5Lean.Proofs.Proof_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.exists_measurable_frame :
    ∃ F₁ F₂ : E3 → E3, Measurable F₁ ∧ Measurable F₂ ∧
    ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p] :=
  @proof_SphereGeom_exists_measurable_frame
