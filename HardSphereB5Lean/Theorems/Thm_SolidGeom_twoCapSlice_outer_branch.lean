import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_outer_branch
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_outer_branch :
    ∀ (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha) (z : ℝ),
    let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
    let h := sqrt D / sin alpha
    let Ck := sqrt (1 - k ^ 2)
    let Cl := sqrt (1 - l ^ 2)
    let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
    let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
    h ≤ z → z ≤ min Ck Cl →
      max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha))) =
        if l < k * cos alpha then 2 * f z
        else if k < l * cos alpha then 2 * g z else 0 :=
  @proof_SolidGeom_twoCapSlice_outer_branch
