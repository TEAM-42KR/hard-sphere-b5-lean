import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_partial_branch
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_partial_branch :
    ∀ (k l alpha z : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hzk : z ^ 2 < 1 - k ^ 2) (hzl : z ^ 2 < 1 - l ^ 2)
    (hDz : 0 < sin alpha ^ 2 * (1 - z ^ 2) - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha), max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
      (min (2 * arccos (l / sqrt (1 - z ^ 2)))
        (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha))) =
      arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha :=
  @proof_SolidGeom_twoCapSlice_partial_branch
