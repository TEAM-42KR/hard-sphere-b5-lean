import HardSphereB5Lean.Theorems.Thm_SolidGeom_area_two_cap_slice
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCapSlice_integral
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCap_rhs_normalization
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom

theorem proof_SolidGeom_area_two_cap (x y z : E3)
    (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
        - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2) :
    let a := dist x y ^ 2
    let b := dist x z ^ 2
    let cc := dist y z ^ 2
    let Q := 4 * a * b - (a + b - cc) ^ 2 - a * b * cc
    (sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1)).toReal =
      2 * π - 2 * Complex.arg ⟨2 * (a + b - cc) - a * b, 2 * √Q⟩
        - √a * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩
        - √b * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩ := by
  let a := dist x y ^ 2
  let b := dist x z ^ 2
  let c := dist y z ^ 2
  let k := sqrt a / 2
  let l := sqrt b / 2
  let alpha := arccos ((a + b - c) / (2 * sqrt a * sqrt b))
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hc : 0 ≤ c := sq_nonneg _
  have hNorm := SolidGeom.twoCap_rhs_normalization a b c ha hb hc hQ
  dsimp only at hNorm
  obtain ⟨⟨hk0, hk1, hl0, hl1, ha0, hap, hD⟩, heq⟩ := hNorm
  have hScalar := SolidGeom.twoCapSlice_integral k l alpha hk0 hk1 hl0 hl1 ha0 hap hD
  have hSlice := SolidGeom.area_two_cap_slice x y z hQ
  exact hSlice.trans (hScalar.trans heq.symm)
