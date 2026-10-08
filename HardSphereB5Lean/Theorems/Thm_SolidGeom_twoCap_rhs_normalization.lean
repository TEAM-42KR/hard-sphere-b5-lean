import HardSphereB5Lean.Proofs.Proof_SolidGeom_twoCap_rhs_normalization
import Mathlib
set_option autoImplicit false

theorem SolidGeom.twoCap_rhs_normalization :
    ∀ (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hQ : 0 < 4 * a * b - (a + b - c) ^ 2 - a * b * c),
    let Q := 4 * a * b - (a + b - c) ^ 2 - a * b * c
  let k := Real.sqrt a / 2
  let l := Real.sqrt b / 2
  let p := (a + b - c) / (2 * Real.sqrt a * Real.sqrt b)
  let alpha := Real.arccos p
  let D := Real.sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * Real.cos alpha
  (0 < k ∧ k < 1 ∧ 0 < l ∧ l < 1 ∧ 0 < alpha ∧ alpha < Real.pi ∧ 0 < D) ∧
  (2 * Real.pi - 2 * Complex.arg ⟨2 * (a + b - c) - a * b, 2 * Real.sqrt Q⟩
    - Real.sqrt a * Complex.arg ⟨Real.sqrt a * (b + c - a), 2 * Real.sqrt Q⟩
    - Real.sqrt b * Complex.arg ⟨Real.sqrt b * (a + c - b), 2 * Real.sqrt Q⟩ =
   2 * Real.pi - 2 * Complex.arg ⟨Real.cos alpha - k * l, Real.sqrt D⟩
    - 2 * k * Complex.arg ⟨l - k * Real.cos alpha, Real.sqrt D⟩
    - 2 * l * Complex.arg ⟨k - l * Real.cos alpha, Real.sqrt D⟩) :=
  @proof_SolidGeom_twoCap_rhs_normalization
