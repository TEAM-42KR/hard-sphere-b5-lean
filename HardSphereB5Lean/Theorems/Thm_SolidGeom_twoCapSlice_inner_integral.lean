import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_inner_integral
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_inner_integral :
    ∀ (k l alpha t : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha)
    (ht0 : 0 ≤ t)
    (ht : t ^ 2 < (sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) / sin alpha ^ 2), (∫ z in (0 : ℝ)..t, max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
      (min (2 * arccos (l / sqrt (1 - z ^ 2)))
        (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha)))) =
      t * (arccos (k / sqrt (1 - t ^ 2)) + arccos (l / sqrt (1 - t ^ 2)) - alpha) +
      arctan (k * t / sqrt (1 - k ^ 2 - t ^ 2)) +
      arctan (l * t / sqrt (1 - l ^ 2 - t ^ 2)) -
      k * arcsin (t / sqrt (1 - k ^ 2)) - l * arcsin (t / sqrt (1 - l ^ 2)) :=
  @proof_SolidGeom_twoCapSlice_inner_integral
