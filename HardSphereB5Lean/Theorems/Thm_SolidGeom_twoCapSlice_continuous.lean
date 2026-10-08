import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_continuous
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_continuous :
    ∀ (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1), ContinuousOn (fun z : ℝ => max 0 (min (2 * arccos (k / sqrt (1 - z ^ 2)))
        (min (2 * arccos (l / sqrt (1 - z ^ 2)))
          (arccos (k / sqrt (1 - z ^ 2)) + arccos (l / sqrt (1 - z ^ 2)) - alpha))))
      (Set.Icc (0 : ℝ) (min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2)))) :=
  @proof_SolidGeom_twoCapSlice_continuous
