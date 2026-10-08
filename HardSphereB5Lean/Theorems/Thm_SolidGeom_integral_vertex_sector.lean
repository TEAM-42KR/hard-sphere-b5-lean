import HardSphereB5Lean.Proofs.Proof_SolidGeom_integral_vertex_sector
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.integral_vertex_sector :
    ∀ (R α : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hα0 : 0 ≤ α) (hα : α < π), ∫ t in (0 : ℝ)..α, (2 / 3 * √(1 - R ^ 2) ^ 3 + (R * cos t) ^ 2 * √(1 - R ^ 2)
        - R * cos t * (√(1 - R ^ 2) ^ 2 + (R * cos t) ^ 2) * (π / 2 - arctan (R * cos t / √(1 - R ^ 2)))) =
      2 / 3 * Complex.arg ⟨cos α, √(1 - R ^ 2) * sin α⟩
        - (2 * R * sin α - (2 * R * sin α) ^ 3 / 12) / 2 * Complex.arg ⟨R * cos α, √(1 - R ^ 2)⟩
        + √(1 - R ^ 2) * R ^ 2 * sin (2 * α) / 6 :=
  @proof_SolidGeom_integral_vertex_sector
