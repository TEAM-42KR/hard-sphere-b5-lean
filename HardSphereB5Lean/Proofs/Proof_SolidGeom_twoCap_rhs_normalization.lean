import Mathlib
set_option autoImplicit false

private theorem q_positive_parameters (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
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

theorem proof_SolidGeom_twoCap_rhs_normalization (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hQ : 0 < 4 * a * b - (a + b - c) ^ 2 - a * b * c) :
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
    - 2 * l * Complex.arg ⟨k - l * Real.cos alpha, Real.sqrt D⟩) := by
  dsimp only
  let s := Real.sqrt a
  let t := Real.sqrt b
  let Q := 4 * a * b - (a + b - c) ^ 2 - a * b * c
  let k := s / 2
  let l := t / 2
  let p := (a + b - c) / (2 * s * t)
  let alpha := Real.arccos p
  let D := Real.sin alpha ^ 2 - k ^ 2 - l ^ 2 + 2 * k * l * Real.cos alpha
  change (0 < k ∧ k < 1 ∧ 0 < l ∧ l < 1 ∧ 0 < alpha ∧ alpha < Real.pi ∧ 0 < D) ∧ _
  obtain ⟨hap, ha4, hbp, hb4, hcp, hc4, hdisc⟩ := q_positive_parameters a b c ha hb hc hQ
  have hs : 0 < s := Real.sqrt_pos.2 hap
  have ht : 0 < t := Real.sqrt_pos.2 hbp
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha
  have ht2 : t ^ 2 = b := Real.sq_sqrt hb
  have hk : 0 < k := by dsimp [k]; positivity
  have hl : 0 < l := by dsimp [l]; positivity
  have hk1 : k < 1 := by dsimp [k]; nlinarith only [ha4, hs2, hs]
  have hl1 : l < 1 := by dsimp [l]; nlinarith only [hb4, ht2, ht]
  have hden : 0 < 2 * s * t := by positivity
  have hpden : p * (2 * s * t) = a + b - c := by
    dsimp [p]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have hden2 : (2 * s * t) ^ 2 = 4 * a * b := by
    calc
      (2 * s * t) ^ 2 = 4 * s ^ 2 * t ^ 2 := by ring
      _ = 4 * a * b := by rw [hs2, ht2]
  have hpden2 : p ^ 2 * (2 * s * t) ^ 2 = (a + b - c) ^ 2 := by
    rw [← mul_pow, hpden]
  have hp2 : p ^ 2 < 1 := by
    by_contra h
    have hz : 0 ≤ (p ^ 2 - 1) * (2 * s * t) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith only [hdisc, hden2, hpden2, hz]
  have hpm : -1 < p := by nlinarith only [hp2, sq_nonneg (p + 1)]
  have hpp : p < 1 := by nlinarith only [hp2, sq_nonneg (p - 1)]
  have halpha : 0 < alpha := Real.arccos_pos.2 hpp
  have halphapi : alpha < Real.pi := Real.arccos_lt_pi.2 hpm
  have hcos : Real.cos alpha = p := Real.cos_arccos hpm.le hpp.le
  have hsin : Real.sin alpha ^ 2 = 1 - p ^ 2 := by
    have H := Real.sin_sq_add_cos_sq alpha
    rw [hcos] at H
    linarith only [H]
  have hc_eq : c = s ^ 2 + t ^ 2 - 2 * s * t * p := by
    nlinarith only [hpden, hs2, ht2]
  have hd : D = 1 - p ^ 2 - s ^ 2 / 4 - t ^ 2 / 4 + s * t * p / 2 := by
    dsimp only [D]
    rw [hsin, hcos]
    dsimp only [k, l]
    ring
  have hQD : Q = 4 * a * b * D := by
    dsimp only [Q]
    rw [← hs2, ← ht2, hc_eq, hd]
    ring
  have hab4 : 0 < 4 * a * b := by positivity
  have hQp : 0 < Q := hQ
  have hDp : 0 < D := by
    have h := hQp
    rw [hQD] at h
    exact (mul_pos_iff_of_pos_left hab4).1 h
  have hroot2 : (2 * s * t * Real.sqrt D) ^ 2 = Q := by
    calc
      (2 * s * t * Real.sqrt D) ^ 2 = 4 * s ^ 2 * t ^ 2 * (Real.sqrt D) ^ 2 := by ring
      _ = 4 * a * b * D := by rw [hs2, ht2, Real.sq_sqrt hDp.le]
      _ = Q := hQD.symm
  have hroot : Real.sqrt Q = 2 * s * t * Real.sqrt D := by
    have hnonneg : 0 ≤ 2 * s * t * Real.sqrt D := by positivity
    nlinarith only [Real.sq_sqrt hQp.le, Real.sqrt_nonneg Q, hroot2, hnonneg]
  let R := 4 * s * t
  have hR : 0 < R := by dsimp only [R]; positivity
  have him : R * Real.sqrt D = 2 * Real.sqrt Q := by dsimp only [R]; rw [hroot]; ring
  have hx0 : R * (Real.cos alpha - k * l) = 2 * (a + b - c) - a * b := by
    rw [hcos]
    calc
      R * (p - k * l) = 2 * (p * (2 * s * t)) - s ^ 2 * t ^ 2 := by dsimp only [R, k, l]; ring
      _ = 2 * (a + b - c) - a * b := by rw [hpden, hs2, ht2]
  have hx1 : R * (l - k * Real.cos alpha) = s * (b + c - a) := by
    rw [hcos]
    calc
      R * (l - k * p) = s * (t ^ 2 + (s ^ 2 + t ^ 2 - 2 * s * t * p) - s ^ 2) := by
        dsimp only [R, k, l]; ring
      _ = s * (b + c - a) := by rw [← hc_eq, hs2, ht2]
  have hx2 : R * (k - l * Real.cos alpha) = t * (a + c - b) := by
    rw [hcos]
    calc
      R * (k - l * p) = t * (s ^ 2 + (s ^ 2 + t ^ 2 - 2 * s * t * p) - t ^ 2) := by
        dsimp only [R, k, l]; ring
      _ = t * (a + c - b) := by rw [← hc_eq, hs2, ht2]
  have harg (x y : ℝ) :
      Complex.arg ⟨R * x, R * y⟩ = Complex.arg ⟨x, y⟩ := by
    have he : (⟨R * x, R * y⟩ : ℂ) = (R : ℂ) * (⟨x, y⟩ : ℂ) := by
      apply Complex.ext <;> simp
    rw [he, Complex.arg_real_mul _ hR]
  have ha0 : Complex.arg ⟨2 * (a + b - c) - a * b, 2 * Real.sqrt Q⟩ =
      Complex.arg ⟨Real.cos alpha - k * l, Real.sqrt D⟩ := by
    rw [← hx0, ← him]
    exact harg _ _
  have ha1 : Complex.arg ⟨s * (b + c - a), 2 * Real.sqrt Q⟩ =
      Complex.arg ⟨l - k * Real.cos alpha, Real.sqrt D⟩ := by
    rw [← hx1, ← him]
    exact harg _ _
  have ha2 : Complex.arg ⟨t * (a + c - b), 2 * Real.sqrt Q⟩ =
      Complex.arg ⟨k - l * Real.cos alpha, Real.sqrt D⟩ := by
    rw [← hx2, ← him]
    exact harg _ _
  constructor
  · exact ⟨hk, hk1, hl, hl1, halpha, halphapi, hDp⟩
  · change 2 * Real.pi - 2 * Complex.arg ⟨2 * (a + b - c) - a * b, 2 * Real.sqrt Q⟩
      - s * Complex.arg ⟨s * (b + c - a), 2 * Real.sqrt Q⟩
      - t * Complex.arg ⟨t * (a + c - b), 2 * Real.sqrt Q⟩ =
      2 * Real.pi - 2 * Complex.arg ⟨Real.cos alpha - k * l, Real.sqrt D⟩
      - 2 * k * Complex.arg ⟨l - k * Real.cos alpha, Real.sqrt D⟩
      - 2 * l * Complex.arg ⟨k - l * Real.cos alpha, Real.sqrt D⟩
    rw [ha0, ha1, ha2]
    dsimp only [k, l]
    ring
