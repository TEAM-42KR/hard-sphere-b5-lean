import HardSphereB5Lean.Proofs.Proof_SolidGeom_beta_inscribed
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.beta_inscribed :
    ∀ (R x y z : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hs : x + y + z = π), Complex.arg ⟨(2 * R * sin x) * (4 * R ^ 2 * sin z ^ 2 + 4 * R ^ 2 * sin y ^ 2 - 4 * R ^ 2 * sin x ^ 2),
        2 * (2 * √(1 - R ^ 2) * R ^ 2 * (sin (2 * x) + sin (2 * y) + sin (2 * z)))⟩ =
      Complex.arg ⟨R * cos x, √(1 - R ^ 2)⟩ :=
  @proof_SolidGeom_beta_inscribed
