import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_QA_pos_of_support {X Y s : ℝ} (hX : 0 < X) (hX1 : X < 1)
    (hY : 0 < Y) (hY1 : Y < 1) (hs : 0 < s) (hH : 0 < Hpoly X Y s) :
    0 < -Y^2 + Y*s + 2*Y - s^2 + 2*s - 1 := by
  have id : -Y^2 + Y*s + 2*Y - s^2 + 2*s - 1 =
      Hpoly X Y s + Y*(1-X)*(s+(1-X)+(1-Y)) := by unfold Hpoly; ring
  rw [id]
  positivity

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_H_diagonal (Y s : ℝ) :
    Hpoly Y Y s = (s-(1-Y)^2)*(1+2*Y-s) := by unfold Hpoly; ring

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_P4_diagonal (Y s : ℝ) :
    P4poly Y Y s = (s-(1-Y)^2)*(Y*(6-Y)+3*(1-s)) := by unfold P4poly; ring

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_P4_one (Y s : ℝ) :
    P4poly 1 Y s = Y*(1-Y)^2*(8-3*Y) +
      (s-(1-Y)^2)*(3*(Y*(2-Y)+1-s)+2*Y) := by unfold P4poly; ring

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_P4_chord (X Y s : ℝ) :
    (1-Y)*P4poly X Y s = (1-X)*P4poly Y Y s + (X-Y)*P4poly 1 Y s +
      (1-Y)*Y*(4-Y)*(X-Y)*(1-X) := by unfold P4poly; ring

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_above_diagonal_of_s_lt_wall {X Y s : ℝ} (hX : 0 < X) (hX1 : X < 1)
    (hY : 0 < Y) (hY1 : Y < 1) (hs : 0 < s) (hs1 : s < 1)
    (hH : 0 < Hpoly X Y s) (hw : s < (1-Y)^2) : Y < X := by
  have hd : Hpoly Y Y s < 0 := by
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_H_diagonal]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hw) (by linarith)
  have diff : Hpoly X Y s - Hpoly Y Y s = Y*(X-Y)*(s+3-2*Y-X) := by
    unfold Hpoly; ring
  by_contra hn
  have hxy : X ≤ Y := le_of_not_gt hn
  have hf : 0 < s+3-2*Y-X := by linarith
  have hp : Y*(X-Y)*(s+3-2*Y-X) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hY) (by linarith)) (le_of_lt hf)
  linarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_P4_nonneg_of_s_ge_wall_X_ge_Y {X Y s : ℝ} (hX1 : X < 1)
    (hY : 0 < Y) (hY1 : Y < 1) (hs1 : s < 1)
    (hw : (1-Y)^2 ≤ s) (hxy : Y ≤ X) : 0 ≤ P4poly X Y s := by
  have h6 : 0 < 6-Y := by linarith
  have h8 : 0 < 8-3*Y := by linarith
  have h2Y : 0 < 2-Y := by linarith
  have h4 : 0 < 4-Y := by linarith
  have h1X : 0 < 1-X := by linarith
  have h1Y : 0 < 1-Y := by linarith
  have ht : 0 < 1-s := by linarith
  have hxy0 : 0 ≤ X-Y := by linarith
  have hd : 0 ≤ P4poly Y Y s := by
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_P4_diagonal]
    apply mul_nonneg (by linarith)
    positivity
  have ho : 0 < P4poly 1 Y s := by
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_P4_one]
    have hp : 0 < Y*(1-Y)^2*(8-3*Y) := by positivity
    have hn : 0 ≤ (s-(1-Y)^2)*(3*(Y*(2-Y)+1-s)+2*Y) := by
      apply mul_nonneg (by linarith)
      have hb : 0 < Y*(2-Y)+1-s := by nlinarith [mul_pos hY h2Y]
      positivity
    linarith
  have hi := S5b_HardSphereB5_Lean_Geometry_PathCore_P4_chord X Y s
  have h1 : 0 ≤ (1-X)*P4poly Y Y s := mul_nonneg (by linarith) hd
  have h2 : 0 ≤ (X-Y)*P4poly 1 Y s := mul_nonneg (by linarith) (le_of_lt ho)
  have h3 : 0 ≤ (1-Y)*Y*(4-Y)*(X-Y)*(1-X) := by positivity
  nlinarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_wall_bulk {X Y s : ℝ} (hX : 0 < X) (hX1 : X < 1)
    (hY : 0 < Y) (hY1 : Y < 1) (hs : 0 < s) (hs1 : s < 1)
    (hH : 0 < Hpoly X Y s) (hw : s = (1-Y)^2) : 0 < P4poly X Y s := by
  have h8 : 0 < 8-3*Y := by linarith
  have h4 : 0 < 4-Y := by linarith
  have h1X : 0 < 1-X := by linarith
  have h1Y : 0 < 1-Y := by linarith
  have hid : Hpoly X Y s = -Y*(X-Y)*(X-(2-Y)^2) := by rw [hw]; unfold Hpoly; ring
  have hsq : 1 < (2-Y)^2 := by nlinarith [sq_nonneg (1-Y)]
  have hxy : Y < X := by
    by_contra hn
    have hle : X ≤ Y := le_of_not_gt hn
    have hm : 0 ≤ (X-Y)*(X-(2-Y)^2) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hnprod : -Y*((X-Y)*(X-(2-Y)^2)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hm
    nlinarith [hid]
  have hxy0 : 0 < X-Y := by linarith
  have hd : P4poly Y Y s = 0 := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_P4_diagonal, hw]; ring
  have ho : 0 < P4poly 1 Y s := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_P4_one, hw]; simp only [sub_self, zero_mul, add_zero]; positivity
  have hi := S5b_HardSphereB5_Lean_Geometry_PathCore_P4_chord X Y s
  have hp : 0 < (X-Y)*P4poly 1 Y s := mul_pos (by linarith) ho
  have hn : 0 ≤ (1-Y)*Y*(4-Y)*(X-Y)*(1-X) := by positivity
  rw [hd, mul_zero, zero_add] at hi
  nlinarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_sliver_alternative {X Y s : ℝ} (hX : 0 < X) (hX1 : X < 1)
    (hY : 0 < Y) (hY1 : Y < 1) (hs : 0 < s) (hs1 : s < 1)
    (hH : 0 < Hpoly X Y s) (hP : P4poly X Y s < 0) :
    (Y < X ↔ s < (1-Y)^2) ∧ (X < Y ↔ (1-Y)^2 < s) := by
  have hwne : s ≠ (1-Y)^2 := by
    intro hw
    have hb := S5b_HardSphereB5_Lean_Geometry_PathCore_near_wall_bulk hX hX1 hY hY1 hs hs1 hH hw
    linarith
  have hl : s < (1-Y)^2 → Y < X := S5b_HardSphereB5_Lean_Geometry_PathCore_above_diagonal_of_s_lt_wall hX hX1 hY hY1 hs hs1 hH
  have hr : (1-Y)^2 < s → X < Y := by
    intro hw
    by_contra hn
    have hxy : Y ≤ X := le_of_not_gt hn
    have hb := S5b_HardSphereB5_Lean_Geometry_PathCore_P4_nonneg_of_s_ge_wall_X_ge_Y hX1 hY hY1 hs1 (le_of_lt hw) hxy
    linarith
  constructor
  · constructor
    · intro hxy
      rcases lt_trichotomy s ((1-Y)^2) with hw | hw | hw
      · exact hw
      · exact False.elim (hwne hw)
      · have hh := hr hw; linarith
    · exact hl
  · constructor
    · intro hxy
      rcases lt_trichotomy s ((1-Y)^2) with hw | hw | hw
      · have hh := hl hw; linarith
      · exact False.elim (hwne hw)
      · exact hw
    · exact hr
private def S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA (Y s : ℝ) : ℝ := -Y^2 + Y*s + 2*Y - s^2 + 2*s - 1
private def S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus (Y s : ℝ) : ℝ := (s-2*Y+5-2*Real.sqrt ((3-Y)*S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s/Y))/(4-Y)
private def S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus (Y s : ℝ) : ℝ := (s-2*Y+5+2*Real.sqrt ((3-Y)*S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s/Y))/(4-Y)

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_quarter_discriminant (Y s : ℝ) :
    Y^2*(s+5-2*Y)^2-3*Y*(4-Y)*(s-1)^2 = 4*Y*(3-Y)*S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s := by
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA; ring

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus_gt_one {Y s : ℝ} (hY : 0 < Y) (hY1 : Y < 1) (hs : 0 < s) :
    1 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s := by
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus
  apply (lt_div_iff₀ (by linarith : 0 < 4-Y)).mpr
  nlinarith [Real.sqrt_nonneg ((3-Y)*S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s/Y)]

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_factorization (X : ℝ) {Y s : ℝ} (hY : 0 < Y) (hY1 : Y < 1)
    (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s) :
    P4poly X Y s = Y*(4-Y)*(X-S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s)*(S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s-X) := by
  have hYn : Y ≠ 0 := ne_of_gt hY
  have hdn : 4-Y ≠ 0 := by linarith
  have h3 : 0 < 3-Y := by linarith
  have hr : 0 ≤ (3-Y)*S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s/Y := le_of_lt (div_pos (mul_pos h3 hQ) hY)
  have hsq := Real.sq_sqrt hr
  have hsqY : Y*(Real.sqrt ((3-Y)*S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s/Y))^2 = (3-Y)*S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s := by
    rw [hsq]; field_simp
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus P4poly
  field_simp [hdn]
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA at hsqY ⊢
  linear_combination -4 * hsqY

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_roots {Y s : ℝ} (hY : 0 < Y) (hY1 : Y < 1) (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s) :
    P4poly (S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s) Y s = 0 ∧ P4poly (S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s) Y s = 0 := by
  constructor
  · rw [S5b_HardSphereB5_Lean_Geometry_PathCore_near_factorization _ hY hY1 hQ]; ring
  · rw [S5b_HardSphereB5_Lean_Geometry_PathCore_near_factorization _ hY hY1 hQ]; ring

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_bulk_iff {X Y s : ℝ} (hX1 : X < 1) (hY : 0 < Y)
    (hY1 : Y < 1) (hs : 0 < s) (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s) :
    0 < P4poly X Y s ↔ S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s < X := by
  have hb := S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus_gt_one hY hY1 hs
  have hbp : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s-X := by linarith
  have hy4 : 0 < Y*(4-Y) := mul_pos hY (by linarith)
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_near_factorization X hY hY1 hQ]
  rw [mul_pos_iff_of_pos_right hbp, mul_pos_iff_of_pos_left hy4]
  exact sub_pos

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_sliver_iff {X Y s : ℝ} (hX1 : X < 1) (hY : 0 < Y)
    (hY1 : Y < 1) (hs : 0 < s) (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s) :
    P4poly X Y s < 0 ↔ X < S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s := by
  have hb := S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus_gt_one hY hY1 hs
  have hbp : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s-X := by linarith
  have hy4 : 0 < Y*(4-Y) := mul_pos hY (by linarith)
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_near_factorization X hY hY1 hQ]
  constructor
  · intro hn
    by_contra hnot
    have hsub : 0 ≤ X-S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s := by linarith
    have hprod := mul_nonneg (mul_nonneg (le_of_lt hy4) hsub) (le_of_lt hbp)
    linarith
  · intro hn
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hy4 (by linarith)) hbp
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_lemma64ab {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (hs : 0 < s) (hs1 : s < 1) (hP : P4poly X Y s ≠ 0) :
    P4poly X Y s = Y*(4-Y)*(X-S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s)*(S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s-X) ∧
    1 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s ∧ (0 < P4poly X Y s ↔ S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s < X) := by
  have hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s := S5b_HardSphereB5_Lean_Geometry_PathCore_QA_pos_of_support hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one hs hc.H_pos
  exact ⟨S5b_HardSphereB5_Lean_Geometry_PathCore_near_factorization X hc.Y_pos hc.Y_lt_one hQ,
    S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus_gt_one hc.Y_pos hc.Y_lt_one hs,
    S5b_HardSphereB5_Lean_Geometry_PathCore_near_bulk_iff hc.X_lt_one hc.Y_pos hc.Y_lt_one hs hQ⟩

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_lemma64c {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (hs : 0 < s) (hs1 : s < 1) (hP : P4poly X Y s < 0) :
    (X > Y ↔ s < (1-Y)^2) ∧ (X < Y ↔ s > (1-Y)^2) :=
  S5b_HardSphereB5_Lean_Geometry_PathCore_near_sliver_alternative hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one hs hs1 hc.H_pos hP

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_lemma64_wall {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (hs : 0 < s) (hs1 : s < 1) (hw : s = (1-Y)^2) : 0 < P4poly X Y s :=
  S5b_HardSphereB5_Lean_Geometry_PathCore_near_wall_bulk hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one hs hs1 hc.H_pos hw

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA_eq_Qpoly (Y s : ℝ) : S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA Y s = Qpoly 0 Y s 1 := by
  simp [S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA, Qpoly]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus_eq_Bminus (Y s : ℝ) : S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus Y s = Bminus Y s := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus, Bminus, S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA_eq_Qpoly]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus_eq_Bplus (Y s : ℝ) : S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus Y s = Bplus Y s := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus, Bplus, S5b_HardSphereB5_Lean_Geometry_PathCore_nearQA_eq_Qpoly]
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_near_selector_factorization_of_deps (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s ≠ 0) :
  P4poly X Y s = Y*(4-Y)*(X-Bminus Y s)*(Bplus Y s-X) ∧
  1 < Bplus Y s ∧ (0<P4poly X Y s ↔ Bminus Y s<X) := by
  simpa only [S5b_HardSphereB5_Lean_Geometry_PathCore_nearBminus_eq_Bminus, S5b_HardSphereB5_Lean_Geometry_PathCore_nearBplus_eq_Bplus] using S5b_HardSphereB5_Lean_Geometry_PathCore_lemma64ab hc hs0 hs hP
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_factorization {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s ≠ 0) :
  P4poly X Y s = Y*(4-Y)*(X-Bminus Y s)*(Bplus Y s-X) ∧
  1 < Bplus Y s ∧ (0<P4poly X Y s ↔ Bminus Y s<X) := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_near_selector_factorization_of_deps c X Y s hc hs0 hs hP

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_near_selector_factorization
