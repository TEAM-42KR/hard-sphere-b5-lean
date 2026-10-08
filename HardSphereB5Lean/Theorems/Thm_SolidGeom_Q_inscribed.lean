import HardSphereB5Lean.Proofs.Proof_SolidGeom_Q_inscribed
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.Q_inscribed :
    ∀ (R x y z : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = π), √(4 * (4 * R ^ 2 * sin z ^ 2) * (4 * R ^ 2 * sin y ^ 2)
        - (4 * R ^ 2 * sin z ^ 2 + 4 * R ^ 2 * sin y ^ 2 - 4 * R ^ 2 * sin x ^ 2) ^ 2
        - (4 * R ^ 2 * sin z ^ 2) * (4 * R ^ 2 * sin y ^ 2) * (4 * R ^ 2 * sin x ^ 2)) =
      2 * √(1 - R ^ 2) * R ^ 2 * (sin (2 * x) + sin (2 * y) + sin (2 * z)) :=
  @proof_SolidGeom_Q_inscribed
