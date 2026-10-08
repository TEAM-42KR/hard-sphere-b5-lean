import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCapSlice_arg_conversion
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem SolidGeom.twoCapSlice_arg_conversion :
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
    let Xk := l - k * cos alpha
    let Xl := k - l * cos alpha
    let Tk := if Xk = 0 then π / 2 else arctan (k * h / sqrt (1 - k ^ 2 - h ^ 2))
    let Tl := if Xl = 0 then π / 2 else arctan (l * h / sqrt (1 - l ^ 2 - h ^ 2))
    Complex.arg ⟨Xk, sqrt D⟩ =
        (if Xk < 0 then π - arcsin (h / Ck) else arcsin (h / Ck)) ∧
      Complex.arg ⟨Xl, sqrt D⟩ =
        (if Xl < 0 then π - arcsin (h / Cl) else arcsin (h / Cl)) ∧
      Complex.arg ⟨cos alpha - k * l, sqrt D⟩ =
        (if Xk < 0 then Tk - Tl else if Xl < 0 then Tl - Tk else π - Tk - Tl) :=
  @proof_SolidGeom_twoCapSlice_arg_conversion
