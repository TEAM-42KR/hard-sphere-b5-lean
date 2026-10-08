import Mathlib
set_option autoImplicit false

theorem proof_SolidGeom_Q_positive_parameters (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
 (hQ : 0 < 4 * a * b - (a + b - c) ^ 2 - a * b * c) :
  0 < a ∧ a < 4 ∧ 0 < b ∧ b < 4 ∧ 0 < c ∧ c < 4 ∧
  0 < 4 * a * b - (a + b - c) ^ 2 := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hbc : 0 ≤ b * c := mul_nonneg hb hc
  have habc : 0 ≤ a * b * c := mul_nonneg hab hc
  have hQa : 0 < 4 * b * c - (b + c - a) ^ 2 - b * c * a := by nlinarith only [hQ]
  have hQb : 0 < 4 * a * c - (a + c - b) ^ 2 - a * c * b := by nlinarith only [hQ]
  have hap : 0 < a := by
    by_contra h
    have he : a = 0 := le_antisymm (le_of_not_gt h) ha
    rw [he] at hQ
    nlinarith only [hQ, sq_nonneg (b - c)]
  have hbp : 0 < b := by
    by_contra h
    have he : b = 0 := le_antisymm (le_of_not_gt h) hb
    rw [he] at hQ
    nlinarith only [hQ, sq_nonneg (a - c)]
  have hcp : 0 < c := by
    by_contra h
    have he : c = 0 := le_antisymm (le_of_not_gt h) hc
    rw [he] at hQ
    nlinarith only [hQ, sq_nonneg (a - b)]
  have ha4 : a < 4 := by
    by_contra h
    have hz : 0 ≤ (a - 4) * (b * c) := mul_nonneg (by linarith) hbc
    nlinarith only [hQa, hz, sq_nonneg (b + c - a)]
  have hb4 : b < 4 := by
    by_contra h
    have hz : 0 ≤ (b - 4) * (a * c) := mul_nonneg (by linarith) hac
    nlinarith only [hQb, hz, sq_nonneg (a + c - b)]
  have hc4 : c < 4 := by
    by_contra h
    have hz : 0 ≤ (c - 4) * (a * b) := mul_nonneg (by linarith) hab
    nlinarith only [hQ, hz, sq_nonneg (a + b - c)]
  exact ⟨hap, ha4, hbp, hb4, hcp, hc4, by linarith⟩
