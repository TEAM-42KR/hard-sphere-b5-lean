import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_integral
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_integral :
    ∀ (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha), 2 * (∫ z in (0 : ℝ)..min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)),
      max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
        (min (2 * arccos (l / sqrt (1 - z ^ 2)))
          (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha)))) =
      2 * π - 2 * Complex.arg ⟨cos alpha - k * l, sqrt (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)⟩ -
      2 * k * Complex.arg ⟨l - k * cos alpha, sqrt (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)⟩ -
      2 * l * Complex.arg ⟨k - l * cos alpha, sqrt (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)⟩ :=
  @proof_SolidGeom_twoCapSlice_integral
