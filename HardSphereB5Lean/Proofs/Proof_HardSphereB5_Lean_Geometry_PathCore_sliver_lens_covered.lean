import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 2000000
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem sqdist_inner (x y : Pt) :
    dist x y ^ 2 = inner ℝ (x - y) (x - y) := by
  simp only [dist_eq_norm, real_inner_self_eq_norm_sq]

private theorem sqdist_expand (x y : Pt) :
    dist x y ^ 2 = inner ℝ x x + inner ℝ y y - 2 * inner ℝ x y := by
  rw [sqdist_inner]
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_comm y x]
  ring

private lemma circle_distance_base (y A B : Pt) :
    dist y A ^ 2 = inner ℝ (y-B) (y-B) - 2 * inner ℝ (y-B) (A-B) + inner ℝ (A-B) (A-B) := by
  rw [dist_eq_norm]
  have he : y-A = (y-B)-(A-B) := by abel
  rw [he, norm_sub_sq_real]
  simp only [real_inner_self_eq_norm_sq]

private lemma circle_label_exhaust (i j l : Fin 4) (hij : i ≠ j) :
    l = i ∨ l = j ∨ l = oth1 i j ∨ l = oth2 i j := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all [oth1, oth2]

private lemma circle_retained_A_neg {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (l : Fin 4)
    (hn : nRet c l ≠ 0) : Apoly X Y s l < 0 := by
  have hs := nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l
  rw [if_neg (not_lt_of_ge hP.le)] at hs
  by_contra hh
  exact hn (by simpa only [if_neg hh] using hs)

private theorem circle_power {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (y : Pt) :
    0 < ∑ l : Fin 4, (Apoly X Y s l / (2 * Hpoly X Y s)) *
      (dist y (c l) ^ 2 - 1) := by
  let u : Pt := c 1 - c 0
  let v : Pt := c 2 - c 0
  let w : Pt := c 3 - c 0
  have huu : inner ℝ u u = 1 := by
    rw [← sqdist_inner]
    simpa only [q, u, dist_comm] using hc.q01
  have hvv : inner ℝ v v = 1 := by
    rw [← sqdist_inner]
    simpa only [q, v, dist_comm] using hc.q02
  have hww : inner ℝ w w = Y := by
    rw [← sqdist_inner]
    simpa only [q, w, dist_comm] using hc.q03
  have huv : inner ℝ u v = 1 - X / 2 := by
    have hdist : dist u v ^ 2 = X := by
      simpa only [u, v, q, dist_sub_right] using hc.q12
    rw [sqdist_expand, huu, hvv] at hdist
    linarith
  have huw : inner ℝ u w = Y / 2 := by
    have hdist : dist u w ^ 2 = 1 := by
      simpa only [u, w, q, dist_sub_right] using hc.q13
    rw [sqdist_expand, huu, hww] at hdist
    linarith
  have hvw : inner ℝ v w = (1 + Y - s) / 2 := by
    have hdist : dist v w ^ 2 = s := by
      simpa only [v, w, q, dist_sub_right] using hc.q23
    rw [sqdist_expand, hvv, hww] at hdist
    linarith
  have hvu : inner ℝ v u = 1 - X / 2 := by exact (real_inner_comm _ _).trans huv
  have hwu : inner ℝ w u = Y / 2 := by exact (real_inner_comm _ _).trans huw
  have hwv : inner ℝ w v = (1 + Y - s) / 2 := by exact (real_inner_comm _ _).trans hvw
  have hH : Hpoly X Y s ≠ 0 := ne_of_gt hc.H_pos
  let a : ℝ := (-X * Y ^ 2 + X * Y * s + X * Y - Y * s + Y - s ^ 2 + 2 * s - 1) /
    (2 * Hpoly X Y s)
  let b : ℝ := Y * (-X * Y + 2 * X + s - 1) / (2 * Hpoly X Y s)
  let d : ℝ := X * (-X * Y + 2 * Y + s - 1) / (2 * Hpoly X Y s)
  let z : Pt := a • u + b • v + d • w
  have hzu : inner ℝ z u = 1 / 2 := by
    simp only [z, inner_add_left, real_inner_smul_left, huu, hvu, hwu]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly
    ring
  have hzv : inner ℝ z v = 1 / 2 := by
    simp only [z, inner_add_left, real_inner_smul_left, huv, hvv, hwv]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly
    ring
  have hzw : inner ℝ z w = Y / 2 := by
    simp only [z, inner_add_left, real_inner_smul_left, huw, hvw, hww]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly
    ring
  have hzz : inner ℝ z z = 1 - P4poly X Y s / (4 * Hpoly X Y s) := by
    change inner ℝ z (a • u + b • v + d • w) = _
    simp only [inner_add_right, real_inner_smul_right, hzu, hzv, hzw]
    dsimp [a, b, d]
    field_simp [hH]
    unfold Hpoly P4poly
    ring
  have hlin : inner ℝ z z = a / 2 + b / 2 + d * (Y / 2) := by
    change inner ℝ z (a • u + b • v + d • w) = _
    simp only [inner_add_right, real_inner_smul_right, hzu, hzv, hzw]
    ring
  rw [hzz] at hlin
  have hA0 : Apoly X Y s 0 / (2 * Hpoly X Y s) = 1 - a - b - d := by
    dsimp [Apoly, a, b, d]
    field_simp [hH]
    unfold Hpoly
    ring
  have hA1 : Apoly X Y s 1 / (2 * Hpoly X Y s) = a := rfl
  have hA2 : Apoly X Y s 2 / (2 * Hpoly X Y s) = b := rfl
  have hA3 : Apoly X Y s 3 / (2 * Hpoly X Y s) = d := rfl
  let t : Pt := y - c 0
  have hd0 : dist y (c 0) ^ 2 = inner ℝ t t := sqdist_inner _ _
  have hd1 : dist y (c 1) ^ 2 = inner ℝ t t - 2 * inner ℝ t u + 1 := by
    have hd := circle_distance_base y (c 1) (c 0)
    change dist y (c 1) ^ 2 = inner ℝ t t - 2 * inner ℝ t u + inner ℝ u u at hd
    simpa only [huu] using hd
  have hd2 : dist y (c 2) ^ 2 = inner ℝ t t - 2 * inner ℝ t v + 1 := by
    have hd := circle_distance_base y (c 2) (c 0)
    change dist y (c 2) ^ 2 = inner ℝ t t - 2 * inner ℝ t v + inner ℝ v v at hd
    simpa only [hvv] using hd
  have hd3 : dist y (c 3) ^ 2 = inner ℝ t t - 2 * inner ℝ t w + Y := by
    have hd := circle_distance_base y (c 3) (c 0)
    change dist y (c 3) ^ 2 = inner ℝ t t - 2 * inner ℝ t w + inner ℝ w w at hd
    simpa only [hww] using hd
  have htz : inner ℝ t z = a * inner ℝ t u + b * inner ℝ t v + d * inner ℝ t w := by
    simp only [z, inner_add_right, real_inner_smul_right]
  have hzt : inner ℝ z t = inner ℝ t z := real_inner_comm _ _
  have hp : (∑ l : Fin 4, (Apoly X Y s l / (2 * Hpoly X Y s)) *
      (dist y (c l) ^ 2 - 1)) = inner ℝ (t - z) (t - z) - P4poly X Y s / (4 * Hpoly X Y s) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (Apoly X Y s 0 / (2 * Hpoly X Y s)) * (dist y (c 0)^2 - 1) +
      ((Apoly X Y s 1 / (2 * Hpoly X Y s)) * (dist y (c 1)^2 - 1) +
        ((Apoly X Y s 2 / (2 * Hpoly X Y s)) * (dist y (c 2)^2 - 1) +
          (Apoly X Y s 3 / (2 * Hpoly X Y s)) * (dist y (c 3)^2 - 1))) = _
    rw [hA0, hA1, hA2, hA3, hd0, hd1, hd2, hd3]
    simp only [inner_sub_left, inner_sub_right]
    rw [hzt, htz, hzz]
    linear_combination -2 * hlin
  rw [hp]
  have hn : 0 ≤ inner ℝ (t - z) (t - z) := real_inner_self_nonneg
  have hnP : P4poly X Y s / (4 * Hpoly X Y s) < 0 :=
    div_neg_of_neg_of_pos hP (mul_pos (by norm_num) hc.H_pos)
  linarith only [hn, hnP]

private lemma circle_count_four (f : Fin 4 → ℕ) (i j : Fin 4) (hij : i ≠ j) :
    (∑ l : Fin 4, f l) = f i + f j + f (oth1 i j) + f (oth2 i j) := by
  fin_cases i <;> fin_cases j <;> simp_all [oth1, oth2, Fin.sum_univ_succ] <;> omega

private lemma circle_unretained_A_nonneg {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (l : Fin 4)
    (hn : nRet c l = 0) : 0 ≤ Apoly X Y s l := by
  by_contra hh
  have ha : Apoly X Y s l < 0 := lt_of_not_ge hh
  have hs := nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l
  rw [if_neg (not_lt_of_ge hP.le), if_pos ha] at hs
  omega

theorem proof_HardSphereB5_Lean_Geometry_PathCore_sliver_lens_covered {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4) (hij : i≠j) (hcom : isCommon c i j) :
  body c {i,j} ⊆ Metric.closedBall (c (oth1 i j)) 1 ∪ Metric.closedBall (c (oth2 i j)) 1 := by
  intro y hy
  have hAk : Apoly X Y s (oth1 i j) < 0 := circle_retained_A_neg hc hP _ hcom.1
  have hAl : Apoly X Y s (oth2 i j) < 0 := circle_retained_A_neg hc hP _ hcom.2
  have hnk : nRet c (oth1 i j) = 2 := by
    rw [nRet_coordinate_selector c X Y s hc (ne_of_lt hP) _,
      if_neg (not_lt_of_ge hP.le), if_pos hAk]
  have hnl : nRet c (oth2 i j) = 2 := by
    rw [nRet_coordinate_selector c X Y s hc (ne_of_lt hP) _,
      if_neg (not_lt_of_ge hP.le), if_pos hAl]
  have hcnt : (∑ l : Fin 4, nRet c l) = 4 := (sliver_incidence hc hP).2.1
  rw [circle_count_four (nRet c) i j hij, hnk, hnl] at hcnt
  have hni : nRet c i = 0 := by omega
  have hnj : nRet c j = 0 := by omega
  have hAi : 0 ≤ Apoly X Y s i := circle_unretained_A_nonneg hc hP _ hni
  have hAj : 0 ≤ Apoly X Y s j := circle_unretained_A_nonneg hc hP _ hnj
  by_contra hh
  have hout : y ∉ Metric.closedBall (c (oth1 i j)) 1 ∧
      y ∉ Metric.closedBall (c (oth2 i j)) 1 := by simpa only [Set.mem_union, not_or] using hh
  have hk : 1 < dist y (c (oth1 i j)) := lt_of_not_ge (fun h => hout.1 (Metric.mem_closedBall.mpr h))
  have hl : 1 < dist y (c (oth2 i j)) := lt_of_not_ge (fun h => hout.2 (Metric.mem_closedBall.mpr h))
  have hki : 0 < dist y (c (oth1 i j)) ^ 2 - 1 := by nlinarith only [hk]
  have hli : 0 < dist y (c (oth2 i j)) ^ 2 - 1 := by nlinarith only [hl]
  have hHi : 0 < 2 * Hpoly X Y s := mul_pos (by norm_num) hc.H_pos
  have hwi : 0 ≤ Apoly X Y s i / (2 * Hpoly X Y s) := div_nonneg hAi hHi.le
  have hwj : 0 ≤ Apoly X Y s j / (2 * Hpoly X Y s) := div_nonneg hAj hHi.le
  have hwk : Apoly X Y s (oth1 i j) / (2 * Hpoly X Y s) < 0 := div_neg_of_neg_of_pos hAk hHi
  have hwl : Apoly X Y s (oth2 i j) / (2 * Hpoly X Y s) < 0 := div_neg_of_neg_of_pos hAl hHi
  have hmem : ∀ l ∈ ({i, j} : Finset (Fin 4)), dist y (c l) ≤ 1 := by
    simpa only [body, Set.mem_iInter, Metric.mem_closedBall] using hy
  have hi : dist y (c i) ^ 2 - 1 ≤ 0 := by
    have hid := hmem i (by simp)
    nlinarith only [hid, dist_nonneg (x := y) (y := c i)]
  have hj : dist y (c j) ^ 2 - 1 ≤ 0 := by
    have hjd := hmem j (by simp)
    nlinarith only [hjd, dist_nonneg (x := y) (y := c j)]
  have hsum : (∑ l : Fin 4, (Apoly X Y s l / (2 * Hpoly X Y s)) *
      (dist y (c l) ^ 2 - 1)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro l _
    rcases circle_label_exhaust i j l hij with rfl | rfl | rfl | rfl
    · exact mul_nonpos_of_nonneg_of_nonpos hwi hi
    · exact mul_nonpos_of_nonneg_of_nonpos hwj hj
    · exact le_of_lt (mul_neg_of_neg_of_pos hwk hki)
    · exact le_of_lt (mul_neg_of_neg_of_pos hwl hli)
  exact (not_le_of_gt (circle_power hc hP y)) hsum

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_sliver_lens_covered
