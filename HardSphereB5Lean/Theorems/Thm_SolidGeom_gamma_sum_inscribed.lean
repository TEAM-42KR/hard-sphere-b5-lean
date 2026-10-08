import HardSphereB5Lean.Proofs.Proof_SolidGeom_gamma_sum_inscribed
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.gamma_sum_inscribed :
    ∀ (R x y z : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hs : x + y + z = π),
    let S : ℝ → ℝ := fun t => 4 * R ^ 2 * sin t ^ 2
    let q := 2 * (2 * √(1 - R ^ 2) * R ^ 2 * (sin (2 * x) + sin (2 * y) + sin (2 * z)))
    Complex.arg ⟨2 * (S z + S y - S x) - S z * S y, q⟩
      + Complex.arg ⟨2 * (S x + S z - S y) - S x * S z, q⟩
      + Complex.arg ⟨2 * (S y + S x - S z) - S y * S x, q⟩ =
      3 * π - 2 * (Complex.arg ⟨cos x, √(1 - R ^ 2) * sin x⟩ + Complex.arg ⟨cos y, √(1 - R ^ 2) * sin y⟩
        + Complex.arg ⟨cos z, √(1 - R ^ 2) * sin z⟩) :=
  @proof_SolidGeom_gamma_sum_inscribed
