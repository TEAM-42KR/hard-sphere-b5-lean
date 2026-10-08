import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_threshold
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_threshold :
    ∀ (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha),
    let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
    let h := sqrt D / sin alpha
    0 < h ∧ h ≤ min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)) ∧
      1 - k ^ 2 - h ^ 2 = (l - k * cos alpha) ^ 2 / sin alpha ^ 2 ∧
      1 - l ^ 2 - h ^ 2 = (k - l * cos alpha) ^ 2 / sin alpha ^ 2 :=
  @proof_SolidGeom_twoCapSlice_threshold
