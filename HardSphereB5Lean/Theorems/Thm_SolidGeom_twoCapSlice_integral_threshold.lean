import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_integral_threshold
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_integral_threshold :
    ∀ (k l alpha : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (hap : alpha < π)
    (hD : 0 < sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha),
    let D := sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * cos alpha
    let h := sqrt D / sin alpha
    let Ck := sqrt (1 - k ^ 2)
    let Cl := sqrt (1 - l ^ 2)
    let f := fun z : ℝ => arccos (k / sqrt (1 - z ^ 2))
    let g := fun z : ℝ => arccos (l / sqrt (1 - z ^ 2))
    let Tk := if l - k * cos alpha = 0 then π / 2
      else arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2))
    let Tl := if k - l * cos alpha = 0 then π / 2
      else arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2))
    (∫ z in (0 : ℝ)..h, max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha)))) =
      h * (f h + g h - alpha) + Tk + Tl -
        k * arcsin (h / Ck) - l * arcsin (h / Cl) :=
  @proof_SolidGeom_twoCapSlice_integral_threshold
