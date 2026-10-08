import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section

open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000

private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (x : Pt) : ℝ := ⟪x, x⟫
private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta (v w : Pt) : ℝ := DeltaT (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v - w))
private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ (v w : Pt) : ℝ := QT (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v - w))
private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center (v w : Pt) : Pt :=
  (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w * (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v - w)) / S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) • v +
  (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v * (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v - w)) / S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) • w
private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height (v w : Pt) : ℝ := Real.sqrt (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w / S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w)
private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal (v w z : Pt) : Pt :=
  if 0 < ⟪z, cross v w⟫ then ‖cross v w‖⁻¹ • cross v w
  else -(‖cross v w‖⁻¹ • cross v w)
private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple (v w : Pt) : Set Pt := {x | ‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1}
private def S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourthThreshold (v w z : Pt) : ℝ :=
  (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq z - 2 * ⟪z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫) / (2 * ⟪z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫)

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq (x : Pt) : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_nonneg (x : Pt) : 0 ≤ S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq x := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq]; positivity
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_sub (x y : Pt) : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (x - y) = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq x + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq y - 2 * ⟪x, y⟫ := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq, inner_sub_left, inner_sub_right, real_inner_comm y x]
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_one_iff (x : Pt) : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq x = 1 ↔ ‖x‖ = 1 := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg x]
  · intro h; rw [h]; norm_num
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_inner_coords (x y : Pt) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1,
      v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := by
  simp [cross, SphereGeom.cross, cross_apply]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_v (v w : Pt) : ⟪v, cross v w⟫ = 0 := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_inner_coords, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_coords]
  simp
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_w (v w : Pt) : ⟪w, cross v w⟫ = 0 := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_inner_coords, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_coords]
  simp
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_sq (v w : Pt) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (cross v w) = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v * S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w - ⟪v, w⟫ ^ 2 := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_inner_coords, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_coords]
  simp
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_gram_resolution (v w x : Pt) :
    (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v * S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w - ⟪v, w⟫ ^ 2) • x =
      (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w * ⟪v, x⟫ - ⟪v, w⟫ * ⟪w, x⟫) • v +
      (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v * ⟪w, x⟫ - ⟪v, w⟫ * ⟪v, x⟫) • w +
      ⟪cross v w, x⟫ • cross v w := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_inner_coords]
  ext i
  fin_cases i <;> simp [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_coords] <;> ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_delta_gram (v w : Pt) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w = 4 * (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v * S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w - ⟪v, w⟫ ^ 2) := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta, DeltaT, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_sub]
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_q_delta (v w : Pt) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v * S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w * S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v - w) := rfl

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_v (v w : Pt) (hD : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w ≠ 0) :
    ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w, v⟫ = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v / 2 := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_delta_gram, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_sub]
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq, real_inner_comm w v]
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_w (v w : Pt) (hD : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w ≠ 0) :
    ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w, w⟫ = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w / 2 := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_delta_gram, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_sub]
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq]
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_sq (v w : Pt) (hD : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w ≠ 0) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v * S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w * S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v - w) / S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w := by
  change ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫ = _
  nth_rw 2 [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_v v w hD, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_w v w hD]
  ring

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_norm_pos (v w : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) : 0 < ‖cross v w‖ := by
  have he := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_delta_gram v w
  have hs := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_sq v w
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cross v w)]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_unit_cross_norm (v w : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) :
    ‖‖cross v w‖⁻¹ • cross v w‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_norm_pos v w hD))]
  exact inv_mul_cancel₀ (ne_of_gt (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_norm_pos v w hD))
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_norm (v w z : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) :
    ‖S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z‖ = 1 := by
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal
  split_ifs <;> simp only [norm_neg, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_unit_cross_norm v w hD]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_sq (v w z : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z) = 1 := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_norm v w z hD]; norm_num
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_v (v w z : Pt) : ⟪v, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ = 0 := by
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal
  split_ifs <;> simp [real_inner_smul_right, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_v]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_w (v w z : Pt) : ⟪w, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ = 0 := by
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal
  split_ifs <;> simp [real_inner_smul_right, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_w]
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_oriented (v w z : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w)
    (hG : ⟪z, cross v w⟫ ≠ 0) : 0 < ⟪z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ := by
  have hi := inv_pos.mpr (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_norm_pos v w hD)
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal
  split_ifs with hz
  · rw [real_inner_smul_right]; exact mul_pos hi hz
  · rw [inner_neg_right, real_inner_smul_right]
    have hz' : ⟪z, cross v w⟫ < 0 := lt_of_le_of_ne (le_of_not_gt hz) hG
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hi hz')
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_normal (v w z : Pt) : ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ = 0 := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center, inner_add_left, real_inner_smul_left, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_v, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_w,
    mul_zero, add_zero]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_perp_as_normal (v w z d : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w)
    (hv : ⟪v, d⟫ = 0) (hw : ⟪w, d⟫ = 0) :
    d = ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z, d⟫ • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z := by
  have hn := ne_of_gt (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_norm_pos v w hD)
  have hsn : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (cross v w) ≠ 0 := by
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq]; exact pow_ne_zero 2 hn
  have hr := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_gram_resolution v w d
  rw [← S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_sq, hv, hw] at hr
  simp only [mul_zero, sub_self, zero_smul, zero_add] at hr
  have hd : d = (⟪cross v w, d⟫ / S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (cross v w)) • cross v w := by
    calc
      d = (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (cross v w))⁻¹ • (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (cross v w) • d) := by
        rw [smul_smul, inv_mul_cancel₀ hsn, one_smul]
      _ = (⟪cross v w, d⟫ / S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (cross v w)) • cross v w := by
        rw [hr, smul_smul]; congr 1; ring
  have hc : d = ⟪‖cross v w‖⁻¹ • cross v w, d⟫ • (‖cross v w‖⁻¹ • cross v w) := by
    calc
      d = (⟪cross v w, d⟫ / S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (cross v w)) • cross v w := hd
      _ = ⟪‖cross v w‖⁻¹ • cross v w, d⟫ • (‖cross v w‖⁻¹ • cross v w) := by
        rw [real_inner_smul_left, smul_smul]
        congr 1
        rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq]
        field_simp [hn]
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal
  split_ifs
  · exact hc
  · simpa only [inner_neg_left, neg_smul, smul_neg, neg_neg] using hc

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height_pos (v w : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) :
    0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w := Real.sqrt_pos.mpr (div_pos hQ hD)
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_height (v w : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w ^ 2 = 1 := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_sq v w (ne_of_gt hD)]
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height
  rw [Real.sq_sqrt (le_of_lt (div_pos hQ hD)), S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_q_delta]
  field_simp [ne_of_gt hD]
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_mem_triple_iff (v w x : Pt) :
    x ∈ S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple v w ↔ S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq x = 1 ∧ ⟪x, v⟫ = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v / 2 ∧ ⟪x, w⟫ = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w / 2 := by
  change (‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1) ↔ _
  simp only [← S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_one_iff, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_sub]
  constructor
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_line_sq (v w z : Pt) (r : ℝ) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + r • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z) = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) + r ^ 2 := by
  have ho := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_normal v w z
  have hn : ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ = 1 := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_sq v w z hD
  have ho' : ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫ = 0 := (real_inner_comm (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) _).trans ho
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ho, ho', hn]
  ring
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_line_mem_triple (v w z : Pt) (r : ℝ) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w)
    (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) (hr : r ^ 2 = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w ^ 2) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + r • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z ∈ S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple v w := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_mem_triple_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_line_sq v w z r hD, hr]
    exact S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_height v w hD hQ
  · rw [inner_add_left, real_inner_smul_left, real_inner_comm v (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z),
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_v, mul_zero, add_zero]
    exact S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_v v w (ne_of_gt hD)
  · rw [inner_add_left, real_inner_smul_left, real_inner_comm w (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z),
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_w, mul_zero, add_zero]
    exact S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_w v w (ne_of_gt hD)

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple_exact (v w z : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple v w = {S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z,
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    obtain ⟨hs, hv, hw⟩ := (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_mem_triple_iff v w x).mp hx
    have hvd : ⟪v, x - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫ = 0 := by
      rw [inner_sub_right, real_inner_comm x v, real_inner_comm (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) v, hv,
        S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_v v w (ne_of_gt hD)]
      ring
    have hwd : ⟪w, x - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫ = 0 := by
      rw [inner_sub_right, real_inner_comm x w, real_inner_comm (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) w, hw,
        S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_inner_w v w (ne_of_gt hD)]
      ring
    let r := ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z, x - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫
    have hd := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_perp_as_normal v w z (x - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) hD hvd hwd
    have hxline : x = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + r • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z := by
      calc x = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + (x - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) := by abel
           _ = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + r • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z := by rw [hd]
    have hr : r ^ 2 = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w ^ 2 := by
      rw [hxline, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_line_sq v w z r hD] at hs
      linarith [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_height v w hD hQ]
    have hf : (r - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w) * (r + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w) = 0 := by nlinarith [hr]
    rcases mul_eq_zero.mp hf with hp | hm
    · left; have he : r = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w := by linarith
      simpa only [he] using hxline
    · right; have he : r = -S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w := by linarith
      simpa only [he, neg_smul, sub_eq_add_neg] using hxline
  · rintro (hx | hx)
    · rw [hx]; exact S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_line_mem_triple v w z (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w) hD hQ rfl
    · rw [hx, sub_eq_add_neg, ← neg_smul]
      exact S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_line_mem_triple v w z (-S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w) hD hQ (neg_sq _)

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z) ^ 2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z) ^ 2 -
      inner ℝ w w * (inner ℝ v z) ^ 2 -
      inner ℝ z z * (inner ℝ v w) ^ 2 := by
  change ⟪cross v w, z⟫ ^ 2 = _
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_inner_coords, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_coords]
  simp
  ring

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple_points_ne (v w z : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z ≠
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z := by
  intro he
  have hh := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height_pos v w hD hQ
  have hs : ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ = 1 := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_sq v w z hD
  have hn0 : ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫ = 0 :=
    (real_inner_comm (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w) _).trans (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_normal v w z)
  have hi := congrArg (fun x : Pt => ⟪S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z, x⟫) he
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hs, hn0] at hi
  linarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourth_sq_formula (v w z : Pt) (r : ℝ) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w)
    (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) (hr : r ^ 2 = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w ^ 2) :
    ‖S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + r • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z - z‖ ^ 2 - 1 =
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq z - 2 * ⟪z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w⟫ - 2 * r * ⟪z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ := by
  rw [← S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_sub, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_line_sq v w z r hD,
    inner_add_left, real_inner_smul_left, real_inner_comm z (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w),
    real_inner_comm z (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z), hr]
  linarith [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center_height v w hD hQ]

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourth_mem_iff (v w z : Pt) (r : ℝ) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w)
    (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) (hG : ⟪z, cross v w⟫ ≠ 0)
    (hr : r ^ 2 = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w ^ 2) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + r • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z ∈ Metric.closedBall z 1 ↔
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourthThreshold v w z ≤ r := by
  have hd : 0 < 2 * ⟪z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ :=
    mul_pos (by norm_num) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_oriented v w z hD hG)
  have hf := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourth_sq_formula v w z r hD hQ hr
  rw [Metric.mem_closedBall, dist_eq_norm, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourthThreshold, div_le_iff₀ hd]
  have hn := norm_nonneg (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + r • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z - z)
  constructor <;> intro h <;> nlinarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_oriented_triple_bridge (v w z : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w)
    (hQ : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w) (hG : ⟪z, cross v w⟫ ≠ 0) :
    ‖S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z‖ = 1 ∧
      ⟪v, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ = 0 ∧ ⟪w, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ = 0 ∧
      0 < ⟪z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z⟫ ∧
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple v w = {S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w + S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z,
        S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w - S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w • S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z} :=
  ⟨S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_norm v w z hD, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_v v w z, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_w v w z,
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_oriented v w z hD hG, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple_exact v w z hD hQ⟩

end
end

section
open HardSphereB5.Lean (Pt)

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith

private def S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![DeltaT X 1 s, DeltaT 1 Y s, DeltaT 1 Y 1, DeltaT 1 1 X]

private def S5b_HardSphereB5_Lean_Geometry_PathCore_gramPoly (a b cc d e f : ℝ) : ℝ :=
  4*a*b*d + (a+b-cc)*(a+d-e)*(b+d-f)
    - a*(b+d-f)^2 - b*(a+d-e)^2 - d*(a+b-cc)^2

private def S5b_HardSphereB5_Lean_Geometry_PathCore_faceAPoly (a b cc d e f : ℝ) : ℝ :=
  DeltaT a b cc * d - b*(a-b+cc)*(a+d-e) - a*(b-a+cc)*(b+d-f)

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
    let i := (faceVerts l).1
    let j := (faceVerts l).2.1
    let k := (faceVerts l).2.2
    Qface c l = Qpoly X Y s l ∧
    Deltaf c i j k = S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly X Y s l ∧
    S5b_HardSphereB5_Lean_Geometry_PathCore_faceAPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) = Apoly X Y s l ∧
    S5b_HardSphereB5_Lean_Geometry_PathCore_gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) = Hpoly X Y s := by
  have h10 : q c 1 0 = 1 := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm', hc.q01]
  have h20 : q c 2 0 = 1 := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm', hc.q02]
  have h30 : q c 3 0 = Y := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm', hc.q03]
  have h21 : q c 2 1 = X := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm', hc.q12]
  have h31 : q c 3 1 = 1 := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm', hc.q13]
  have h32 : q c 3 2 = s := by rw [S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm', hc.q23]
  fin_cases l <;>
    dsimp [faceVerts, Qface, Qf, Deltaf, QT, DeltaT, S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly, Qpoly, Apoly,
      S5b_HardSphereB5_Lean_Geometry_PathCore_faceAPoly, S5b_HardSphereB5_Lean_Geometry_PathCore_gramPoly, Hpoly] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hc.q01, hc.q02, hc.q03, hc.q12, hc.q13, hc.q23,
      h10, h20, h30, h21, h31, h32] <;> ring

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_cayley_menger_face_identity (X Y s : ℝ) (l : Fin 4) :
    Apoly X Y s l ^ 2 - 4 * Hpoly X Y s * Qpoly X Y s l =
      -S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly X Y s l * P4poly X Y s := by
  fin_cases l <;> simp [Apoly, Hpoly, Qpoly, S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly, DeltaT, P4poly] <;> ring

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z)^2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z)^2 -
      inner ℝ w w * (inner ℝ v z)^2 -
      inner ℝ z z * (inner ℝ v w)^2 :=
  S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_gram_identity v w z

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_gram_from_q (c : Fin 4 → Pt) (i j k l : Fin 4) :
    4 * (inner ℝ (SphereGeom.cross (c j - c i) (c k - c i)) (c l - c i))^2 =
    S5b_HardSphereB5_Lean_Geometry_PathCore_gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) := by
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_cross_gram_identity, ← S5b_HardSphereB5_Lean_Geometry_PathCore_q_inner, ← S5b_HardSphereB5_Lean_Geometry_PathCore_q_inner, ← S5b_HardSphereB5_Lean_Geometry_PathCore_q_inner,
    S5b_HardSphereB5_Lean_Geometry_PathCore_inner_from_q, S5b_HardSphereB5_Lean_Geometry_PathCore_inner_from_q, S5b_HardSphereB5_Lean_Geometry_PathCore_inner_from_q]
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_gramPoly]
  ring

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_face_det_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
    0 < (inner ℝ (SphereGeom.cross
      (c (faceVerts l).2.1 - c (faceVerts l).1)
      (c (faceVerts l).2.2 - c (faceVerts l).1)) (c l - c (faceVerts l).1))^2 := by
  have hg := S5b_HardSphereB5_Lean_Geometry_PathCore_gram_from_q c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 l
  rw [(S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys c X Y s hc l).2.2.2] at hg
  linarith [hc.H_pos]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_retained_set_eq (c : Fin 4 → Pt) (l : Fin 4) :
    triplePts c l ∩ Kset c = {x | x ∈ triplePts c l ∧ dist x (c l) ≤ 1} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ht, hk⟩
    refine ⟨ht, ?_⟩
    have h := (Set.mem_iInter.mp (Set.mem_iInter.mp hk l)) (Finset.mem_univ l)
    simpa only [Metric.mem_closedBall, dist_comm] using h
  · rintro ⟨ht, hl⟩
    refine ⟨ht, ?_⟩
    simp only [Kset, body, Set.mem_iInter, Finset.mem_univ, true_implies,
      Metric.mem_closedBall]
    intro i
    by_cases hi : i = l
    · simpa [hi, dist_comm] using hl
    · simpa only [dist_comm, ht i hi] using (le_refl (1 : ℝ))

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_counts (c : Fin 4 → Pt) (hn : ∀ l, nRet c l = 1) :
    ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 := by
  intro m
  simp_rw [hn]
  simp

end

section
open HardSphereB5.Lean (Pt)

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_two_point_retained_count (p m z : Pt) (a b : ℝ) (hpm : p ≠ m) (hb : 0 < b)
    (hp : (dist p z)^2 - 1 = a - b) (hm : (dist m z)^2 - 1 = a + b) :
    ({p,m} ∩ Metric.closedBall z 1).ncard =
      if a^2 < b^2 then 1 else if b^2 < a^2 ∧ a < 0 then 2 else
        if b^2 < a^2 then 0 else ({p,m} ∩ Metric.closedBall z 1).ncard := by
  have hp' : p ∈ Metric.closedBall z 1 ↔ a - b ≤ 0 := by
    simp only [Metric.mem_closedBall, dist_comm z]
    constructor <;> intro h <;> nlinarith [(dist_nonneg : 0 ≤ dist p z)]
  have hm' : m ∈ Metric.closedBall z 1 ↔ a + b ≤ 0 := by
    simp only [Metric.mem_closedBall, dist_comm z]
    constructor <;> intro h <;> nlinarith [(dist_nonneg : 0 ≤ dist m z)]
  by_cases hab : a^2 < b^2
  · rw [if_pos hab]
    have ha1 : a - b < 0 := by nlinarith
    have ha2 : 0 < a + b := by nlinarith
    have hs : {p,m} ∩ Metric.closedBall z 1 = {p} := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact (not_le_of_gt ha2 ((hm').mp hx)).elim
      · rintro rfl; exact ⟨Or.inl rfl, hp'.mpr (le_of_lt ha1)⟩
    rw [hs]; simp
  · rw [if_neg hab]
    by_cases hba : b^2 < a^2
    · by_cases ha : a < 0
      · rw [if_pos ⟨hba,ha⟩]
        have ha1 : a - b < 0 := by linarith
        have ha2 : a + b < 0 := by nlinarith
        have hs : {p,m} ∩ Metric.closedBall z 1 = {p,m} := by
          apply Set.inter_eq_left.mpr
          intro x hx
          rcases Set.mem_insert_iff.mp hx with rfl | hx
          · exact hp'.mpr (le_of_lt ha1)
          · have he : x = m := Set.mem_singleton_iff.mp hx
            rw [he]; exact hm'.mpr (le_of_lt ha2)
        rw [hs]; exact Set.ncard_pair hpm
      · rw [if_neg (fun h => ha h.2), if_pos hba]
        have ha1 : 0 < a - b := by nlinarith
        have ha2 : 0 < a + b := by nlinarith
        have hs : {p,m} ∩ Metric.closedBall z 1 = ∅ := by
          ext x; simp only [Set.mem_inter_iff, Set.mem_insert_iff,
            Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          rintro ⟨rfl | rfl,hx⟩
          · exact not_le_of_gt ha1 (hp'.mp hx)
          · exact not_le_of_gt ha2 (hm'.mp hx)
        rw [hs]; simp
    · rw [if_neg (fun h => hba h.1), if_neg hba]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_margin_selector (H D Q P A a b : ℝ) (hH : 0 < H) (hD : 0 < D)
    (hQ : 0 < Q) (hb : 0 < b) (ha : D*a = A)
    (hb2 : D^2*b^2 = 4*H*Q) (hdisc : A^2 - 4*H*Q = -D*P) :
    (0 < P → a^2 < b^2) ∧ (P < 0 → b^2 < a^2) ∧ (a < 0 ↔ A < 0) := by
  have hid : D^2*(a^2-b^2) = -D*P := by
    calc D^2*(a^2-b^2) = (D*a)^2 - D^2*b^2 := by ring
         _ = A^2-4*H*Q := by rw [ha,hb2]
         _ = -D*P := hdisc
  refine ⟨?_, ?_, ?_⟩
  · intro hP
    have hn : -D*P < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hD) hP
    have hdiff : a^2-b^2 < 0 := by
      by_contra h
      have hh := mul_nonneg (sq_nonneg D) (le_of_not_gt h)
      linarith
    linarith
  · intro hP
    have hn : 0 < -D*P := mul_pos_of_neg_of_neg (neg_neg_of_pos hD) hP
    have hdiff : 0 < a^2-b^2 := by
      by_contra h
      have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg D) (le_of_not_gt h)
      linarith
    linarith
  · rw [← ha]
    constructor <;> intro h <;> nlinarith

end

section
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_path_s_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) : 0 < s := by
  have hs : 0 ≤ s := by rw [← hc.q23]; unfold q; positivity
  by_contra h
  have he : s = 0 := le_antisymm (le_of_not_gt h) hs
  have hd : dist (c 2) (c 3) = 0 := by
    have hq := hc.q23
    unfold q at hq
    rw [he] at hq
    nlinarith [(dist_nonneg : 0 ≤ dist (c 2) (c 3))]
  have hcent := dist_eq_zero.mp hd
  have hX := hc.q12
  have hqq : q c 1 2 = q c 1 3 := by simp only [q,hcent]
  rw [hqq,hc.q13] at hX
  linarith [hc.X_lt_one]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_path_Qpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) :
    ∀ l, 0 < Qpoly X Y s l := by
  have hs := S5b_HardSphereB5_Lean_Geometry_PathCore_path_s_pos c X Y s hc
  have h0 : 0 < X * (1-Y) * (s+(1-X)+(1-Y)) :=
    mul_pos (mul_pos hc.X_pos (by linarith [hc.Y_lt_one])) (by linarith [hc.X_lt_one,hc.Y_lt_one])
  have h1 : 0 < Y * (1-X) * (s+(1-X)+(1-Y)) :=
    mul_pos (mul_pos hc.Y_pos (by linarith [hc.X_lt_one])) (by linarith [hc.X_lt_one,hc.Y_lt_one])
  have e0 : Qpoly X Y s 0 = Hpoly X Y s + X*(1-Y)*(s+(1-X)+(1-Y)) := by
    simp [Qpoly,Hpoly]; ring
  have e1 : Qpoly X Y s 1 = Hpoly X Y s + Y*(1-X)*(s+(1-X)+(1-Y)) := by
    simp [Qpoly,Hpoly]; ring
  intro l
  fin_cases l
  · change 0 < Qpoly X Y s 0
    rw [e0]; linarith [hc.H_pos]
  · change 0 < Qpoly X Y s 1
    rw [e1]; linarith [hc.H_pos]
  · simpa [Qpoly] using mul_pos hc.Y_pos (show 0 < 3-Y by linarith [hc.Y_lt_one])
  · simpa [Qpoly] using mul_pos hc.X_pos (show 0 < 3-X by linarith [hc.X_lt_one])

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_q_nonneg' (c : Fin 4 → Pt) (i j : Fin 4) : 0 ≤ q c i j := by unfold q; positivity

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_path_Dpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
    0 < S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly X Y s l := by
  have hQ : 0 < Qface c l := by rw [(S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys c X Y s hc l).1]; exact S5b_HardSphereB5_Lean_Geometry_PathCore_path_Qpoly_pos c X Y s hc l
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  have hd := (S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys c X Y s hc l).2.1
  change Deltaf c i j k = S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly X Y s l at hd
  have hn : 0 ≤ q c i j * q c i k * q c j k :=
    mul_nonneg (mul_nonneg (S5b_HardSphereB5_Lean_Geometry_PathCore_q_nonneg' c i j) (S5b_HardSphereB5_Lean_Geometry_PathCore_q_nonneg' c i k)) (S5b_HardSphereB5_Lean_Geometry_PathCore_q_nonneg' c j k)
  change 0 < Deltaf c i j k - q c i j*q c i k*q c j k at hQ
  linarith

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_norm_sub_base (x y p : Pt) : ‖(x-p)-(y-p)‖ = ‖x-y‖ := by
  congr 1; abel

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_triplePts_translate (c : Fin 4 → Pt) (l : Fin 4) :
    triplePts c l = {x | x - c (faceVerts l).1 ∈
      S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1)} := by
  ext x
  fin_cases l <;>
    simp [triplePts, faceVerts, Fin.forall_fin_succ, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple,
      dist_eq_norm, S5b_HardSphereB5_Lean_Geometry_PathCore_norm_sub_base] <;> tauto

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_q (c : Fin 4 → Pt) (i j : Fin 4) : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (c j-c i) = q c i j := by
  exact (S5b_HardSphereB5_Lean_Geometry_PathCore_q_inner c i j).symm

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_diff_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq ((c j-c i)-(c k-c i)) = q c j k := by
  have he : (c j-c i)-(c k-c i) = c j-c k := by abel
  rw [he, S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_q, S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm']

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_face_TG_D (c : Fin 4 → Pt) (l : Fin 4) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) =
    Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta, S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_q, S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_diff_q, Deltaf]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_face_TG_Q (c : Fin 4 → Pt) (l : Fin 4) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) = Qface c l := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ, S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_q, S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_diff_q, Qface, Qf]

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_normal_projection_identity (v w z : Pt) (hD : 0 < S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w * (inner ℝ z (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z))^2 =
      4 * (inner ℝ z (cross v w))^2 := by
  have hn := ne_of_gt (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_norm_pos v w hD)
  have hd : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w = 4*‖cross v w‖^2 := by
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_delta_gram, ← S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_cross_sq, S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_eq_norm_sq]
  rw [hd]
  unfold S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal
  split_ifs <;> simp only [inner_neg_right, real_inner_smul_right]
  all_goals field_simp [hn]
  all_goals ring

private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_numerator_identity (v w z : Pt) (hD : S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w ≠ 0) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w * (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq z - 2*inner ℝ z (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w)) =
      S5b_HardSphereB5_Lean_Geometry_PathCore_faceAPoly (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v-w))
        (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq z) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (z-v)) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (z-w)) := by
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center, inner_add_right, real_inner_smul_right, S5b_HardSphereB5_Lean_Geometry_PathCore_faceAPoly]
  have hd : DeltaT (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq v) (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq w)
      (S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq (v-w)) = S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w := rfl
  rw [hd]
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq_sub]
  field_simp [hD]
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_delta_gram]
  ring

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (l : Fin 4) :
    nRet c l = if 0 < P4poly X Y s then 1 else if Apoly X Y s l < 0 then 2 else 0 := by
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  let v := c j-c i
  let w := c k-c i
  let z := c l-c i
  let D := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceDelta v w
  let Q := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_faceQ v w
  let N := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_orientedNormal v w z
  let h := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height v w
  let o := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_center v w
  let p := c i + (o+h•N)
  let m := c i + (o-h•N)
  let a := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_sq z - 2*inner ℝ z o
  let b := 2*h*inner ℝ z N
  have hDP : D = S5b_HardSphereB5_Lean_Geometry_PathCore_Dpoly X Y s l := (S5b_HardSphereB5_Lean_Geometry_PathCore_face_TG_D c l).trans (S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys c X Y s hc l).2.1
  have hQP : Q = Qpoly X Y s l := (S5b_HardSphereB5_Lean_Geometry_PathCore_face_TG_Q c l).trans (S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys c X Y s hc l).1
  have hD : 0 < D := by rw [hDP]; exact S5b_HardSphereB5_Lean_Geometry_PathCore_path_Dpoly_pos c X Y s hc l
  have hQ : 0 < Q := by rw [hQP]; exact S5b_HardSphereB5_Lean_Geometry_PathCore_path_Qpoly_pos c X Y s hc l
  have hQface : 0 < Qface c l := by rw [← S5b_HardSphereB5_Lean_Geometry_PathCore_face_TG_Q c l]; exact hQ
  have hdet : 4*(inner ℝ z (cross v w))^2 = Hpoly X Y s := by
    have hg := S5b_HardSphereB5_Lean_Geometry_PathCore_gram_from_q c i j k l
    rw [(S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys c X Y s hc l).2.2.2] at hg
    simpa only [real_inner_comm] using hg
  have hG : inner ℝ z (cross v w) ≠ 0 := by intro hz; rw [hz] at hdet; nlinarith [hc.H_pos]
  have hn : 0 < inner ℝ z N := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_normal_oriented v w z hD hG
  have hh : 0 < h := S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_height_pos v w hD hQ
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hh) hn
  have hpm : p ≠ m := by
    exact fun he => S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple_points_ne v w z hD hQ (add_left_cancel he)
  have htr : triplePts c l = {p,m} := by
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_triplePts_translate c l]
    change {x | x-c i ∈ S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple v w} = {p,m}
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_triple_exact v w z hD hQ]
    ext x
    simp [p,m,o,h,N,Set.mem_insert_iff,Set.mem_singleton_iff,sub_eq_iff_eq_add,add_comm]
  have hp : (dist p (c l))^2-1 = a-b := by
    have he : p-c l = o+h•N-z := by dsimp [p,z]; abel
    rw [dist_eq_norm,he]
    exact S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourth_sq_formula v w z h hD hQ rfl
  have hm : (dist m (c l))^2-1 = a+b := by
    have he : m-c l = o+(-h)•N-z := by dsimp [m,z]; simp only [neg_smul]; abel
    rw [dist_eq_norm,he,S5b_HardSphereB5_Lean_Geometry_PathCore_TripleGeometry_fourth_sq_formula v w z (-h) hD hQ (neg_sq h)]
    dsimp [a,b]; ring
  have ha : D*a = Apoly X Y s l := by
    have hx := S5b_HardSphereB5_Lean_Geometry_PathCore_numerator_identity v w z (ne_of_gt hD)
    change D*a = _ at hx
    dsimp [v,w,z] at hx
    simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_q, S5b_HardSphereB5_Lean_Geometry_PathCore_TG_sq_diff_q] at hx
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm' c l j, S5b_HardSphereB5_Lean_Geometry_PathCore_q_symm' c l k] at hx
    exact hx.trans (S5b_HardSphereB5_Lean_Geometry_PathCore_face_polys c X Y s hc l).2.2.1
  have hhd : D*h^2 = Q := by
    change D * (Real.sqrt (Q/D))^2 = Q
    rw [Real.sq_sqrt (div_nonneg (le_of_lt hQ) (le_of_lt hD))]
    field_simp [ne_of_gt hD]
    <;> ring
  have hnd : D*(inner ℝ z N)^2 = Hpoly X Y s :=
    (S5b_HardSphereB5_Lean_Geometry_PathCore_normal_projection_identity v w z hD).trans hdet
  have hb2 : D^2*b^2 = 4*Hpoly X Y s*Qpoly X Y s l := by
    calc D^2*b^2 = 4*(D*h^2)*(D*(inner ℝ z N)^2) := by dsimp [b]; ring
         _ = 4*Q*Hpoly X Y s := by rw [hhd,hnd]
         _ = 4*Hpoly X Y s*Qpoly X Y s l := by rw [hQP]; ring
  have hdisc : Apoly X Y s l^2 - 4*Hpoly X Y s*Qpoly X Y s l = -D*P4poly X Y s := by
    rw [hDP]; exact S5b_HardSphereB5_Lean_Geometry_PathCore_cayley_menger_face_identity X Y s l
  have hs := S5b_HardSphereB5_Lean_Geometry_PathCore_margin_selector (Hpoly X Y s) D (Qpoly X Y s l) (P4poly X Y s)
    (Apoly X Y s l) a b hc.H_pos hD (S5b_HardSphereB5_Lean_Geometry_PathCore_path_Qpoly_pos c X Y s hc l) hb ha hb2 hdisc
  have hset : triplePts c l ∩ Kset c = {p,m} ∩ Metric.closedBall (c l) 1 := by
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_retained_set_eq,htr]
    ext x; simp [Metric.mem_closedBall,dist_comm]
  rw [nRet,if_pos hQface,hset]
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_two_point_retained_count p m (c l) a b hpm hb hp hm]
  by_cases hbulk : 0 < P4poly X Y s
  · rw [if_pos hbulk, if_pos (hs.1 hbulk)]
  · have hsliv : P4poly X Y s < 0 := lt_of_le_of_ne (le_of_not_gt hbulk) hP
    have hba := hs.2.1 hsliv
    rw [if_neg hbulk,if_neg (not_lt_of_ge (le_of_lt hba))]
    by_cases hA : Apoly X Y s l < 0
    · rw [if_pos hA,if_pos ⟨hba,hs.2.2.mpr hA⟩]
    · rw [if_neg hA,if_neg (fun hh => hA (hs.2.2.mp hh.2)),if_pos hba]

end

section
set_option maxHeartbeats 1000000

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_threshold (X Y t : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (ht : 0 < t) (hYX : Y < X) (hP : P4poly X Y (1-t) < 0) :
    Y*(2-Y) < t := by
  have hT : 0 < Y*(2-Y) := mul_pos hY0 (by linarith)
  have hc : 0 < (4-Y)*(1-X)+(1-Y)*(8-3*Y) := by
    have h4 : 0 < 4-Y := by linarith
    have h8 : 0 < 8-3*Y := by linarith
    have h1X : 0 < 1-X := by linarith
    have h1Y : 0 < 1-Y := by linarith
    positivity
  have he0 : P4poly X Y (1-Y*(2-Y)) =
      Y*(X-Y)*((4-Y)*(1-X)+(1-Y)*(8-3*Y)) := by
    unfold P4poly
    ring
  have hp0 : 0 < P4poly X Y (1-Y*(2-Y)) := by
    rw [he0]
    exact mul_pos (mul_pos hY0 (sub_pos.mpr hYX)) hc
  by_contra hn
  have hle : t ≤ Y*(2-Y) := le_of_not_gt hn
  have hm : 0 ≤ (Y*(2-Y)-t)*(2*X*Y+3*(t+Y*(2-Y))) :=
    mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have he : P4poly X Y (1-t) = P4poly X Y (1-Y*(2-Y)) +
      (Y*(2-Y)-t)*(2*X*Y+3*(t+Y*(2-Y))) := by
    unfold P4poly
    ring
  linarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_support_bound (X Y t : ℝ)
    (hX0 : 0 < X) (hY0 : 0 < Y) (hY1 : Y < 1)
    (ht : 0 < t) (hYX : Y < X) (hH : 0 < Hpoly X Y (1-t)) :
    t < X*(2-Y) := by
  have hU : 0 < X*(2-Y) := mul_pos hX0 (by linarith)
  have hc : 0 < X*(X-Y)*(4-Y) :=
    mul_pos (mul_pos hX0 (sub_pos.mpr hYX)) (by linarith)
  have he0 : Hpoly X Y (1-X*(2-Y)) = -X*(X-Y)*(4-Y) := by
    unfold Hpoly
    ring
  by_contra hn
  have hle : X*(2-Y) ≤ t := le_of_not_gt hn
  have hm : 0 ≤ (t-X*(2-Y))*(X*Y+t+X*(2-Y)) :=
    mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have he : Hpoly X Y (1-t) = Hpoly X Y (1-X*(2-Y)) -
      (t-X*(2-Y))*(X*Y+t+X*(2-Y)) := by
    unfold Hpoly
    ring
  linarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_A1_neg (X Y t : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (ht : 0 < t) (hYX : Y < X) (hP : P4poly X Y (1-t) < 0) :
    Apoly X Y (1-t) 1 < 0 := by
  have h1X : 0 < 1-X := by linarith
  have hTx : 0 < X*(2-X) := mul_pos hX0 (by linarith)
  have hc : 0 < (2-X)^2-Y := by
    nlinarith [sq_nonneg (1-X)]
  have hd : 0 < X*(2-X)-Y*(1-X) := by
    have hp : 0 < (X-Y)*(1-X) := mul_pos (sub_pos.mpr hYX) h1X
    nlinarith
  by_contra hn
  have ha : 0 ≤ Apoly X Y (1-t) 1 := le_of_not_gt hn
  have hlt : t < X*(2-X) := by
    by_contra hn'
    have hle : X*(2-X) ≤ t := le_of_not_gt hn'
    have hm : 0 ≤ (t-X*(2-X))*(t+X*(2-X)-Y*(1-X)) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    have hp : 0 < X*(X-Y)*((2-X)^2-Y) :=
      mul_pos (mul_pos hX0 (sub_pos.mpr hYX)) hc
    have he : Apoly X Y (1-t) 1 =
        -X*(X-Y)*((2-X)^2-Y) -
        (t-X*(2-X))*(t+X*(2-X)-Y*(1-X)) := by
      simp [Apoly] <;> ring <;> simp
    linarith
  have hp : 0 < Y*(3-X)*(X*(2-X)-t)+X*Y*(1-X)*(X-Y) := by
    have h3 : 0 < 3-X := by linarith
    have hdt : 0 < X*(2-X)-t := sub_pos.mpr hlt
    have hxy : 0 < X-Y := sub_pos.mpr hYX
    positivity
  have he : P4poly X Y (1-t) = 3*Apoly X Y (1-t) 1 +
      Y*(3-X)*(X*(2-X)-t)+X*Y*(1-X)*(X-Y) := by
    simp [P4poly, Apoly]
    ring
  linarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_signs_near_gt (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hs1 : s < 1) (hYX : Y < X) :
    0 < Apoly X Y s 0 ∧ Apoly X Y s 1 < 0 ∧
    0 < Apoly X Y s 2 ∧ Apoly X Y s 3 < 0 := by
  let t := 1-s
  have ht : 0 < t := by dsimp [t]; linarith
  have hs : s = 1-t := by dsimp [t]; ring
  rw [hs] at hH hP ⊢
  have hT := S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_threshold X Y t hX0 hX1 hY0 hY1 ht hYX hP
  have hU := S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_support_bound X Y t hX0 hY0 hY1 ht hYX hH
  have hA1 := S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_A1_neg X Y t hX0 hX1 hY0 hY1 ht hYX hP
  have hA0 : 0 < Apoly X Y (1-t) 0 := by
    have hp : 0 < X*(t-Y*(2-Y)) := mul_pos hX0 (sub_pos.mpr hT)
    have he : Apoly X Y (1-t) 0 = Hpoly X Y (1-t)+X*(t-Y*(2-Y)) := by
      simp [Apoly, Hpoly]
      ring
    linarith
  have hA2 : 0 < Apoly X Y (1-t) 2 := by
    have he : Apoly X Y (1-t) 2 = Y*(X*(2-Y)-t) := by
      simp [Apoly] <;> ring <;> simp
    rw [he]
    exact mul_pos hY0 (sub_pos.mpr hU)
  have hA3 : Apoly X Y (1-t) 3 < 0 := by
    have hp : 0 < Y*(X-Y) := mul_pos hY0 (sub_pos.mpr hYX)
    have hL : Y*(2-X) < t := by nlinarith
    have he : Apoly X Y (1-t) 3 = X*(Y*(2-X)-t) := by
      simp [Apoly] <;> ring <;> simp
    rw [he]
    exact mul_neg_of_pos_of_neg hX0 (sub_neg.mpr hL)
  exact ⟨hA0, hA1, hA2, hA3⟩

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_signs_near_lt (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hs1 : s < 1) (hXY : X < Y) :
    Apoly X Y s 0 < 0 ∧ 0 < Apoly X Y s 1 ∧
    Apoly X Y s 2 < 0 ∧ 0 < Apoly X Y s 3 := by
  have hHs : Hpoly Y X s = Hpoly X Y s := by unfold Hpoly; ring
  have hPs : P4poly Y X s = P4poly X Y s := by unfold P4poly; ring
  have hh : 0 < Hpoly Y X s := by rwa [hHs]
  have hp : P4poly Y X s < 0 := by rwa [hPs]
  rcases S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_signs_near_gt Y X s hY0 hY1 hX0 hX1 hh hs0 hp hs1 hXY with
    ⟨ha0, ha1, ha2, ha3⟩
  have he0 : Apoly X Y s 0 = Apoly Y X s 1 := by simp [Apoly] <;> ring <;> simp
  have he1 : Apoly X Y s 1 = Apoly Y X s 0 := by simp [Apoly] <;> ring <;> simp
  have he2 : Apoly X Y s 2 = Apoly Y X s 3 := by simp [Apoly] <;> ring <;> simp
  have he3 : Apoly X Y s 3 = Apoly Y X s 2 := by simp [Apoly] <;> ring <;> simp
  exact ⟨by rwa [he0], by rwa [he1], by rwa [he2], by rwa [he3]⟩

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_signs_far (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hs1 : 1 < s) :
    Apoly X Y s 0 < 0 ∧ Apoly X Y s 1 < 0 ∧
    0 < Apoly X Y s 2 ∧ 0 < Apoly X Y s 3 := by
  let u := s-1
  have hu : 0 < u := by dsimp [u]; linarith
  have hs : s = 1+u := by dsimp [u]; ring
  rw [hs] at hP ⊢
  have h1X : 0 < 1-X := by linarith
  have h1Y : 0 < 1-Y := by linarith
  have h3X : 0 < 3-X := by linarith
  have h3Y : 0 < 3-Y := by linarith
  have h4X : 0 < 4-X := by linarith
  have h4Y : 0 < 4-Y := by linarith
  have hR0 : 0 < X*((3-Y)*u+Y*(2+(4-X)*(1-Y))) := by positivity
  have hR1 : 0 < Y*((3-X)*u+X*(2+(4-Y)*(1-X))) := by positivity
  have he0 : P4poly X Y (1+u) = 3*Apoly X Y (1+u) 0 +
      X*((3-Y)*u+Y*(2+(4-X)*(1-Y))) := by
    simp [P4poly, Apoly]
    ring
  have he1 : P4poly X Y (1+u) = 3*Apoly X Y (1+u) 1 +
      Y*((3-X)*u+X*(2+(4-Y)*(1-X))) := by
    simp [P4poly, Apoly]
    ring
  have ha0 : Apoly X Y (1+u) 0 < 0 := by linarith
  have ha1 : Apoly X Y (1+u) 1 < 0 := by linarith
  have ha2 : 0 < Apoly X Y (1+u) 2 := by
    have he : Apoly X Y (1+u) 2 = Y*(X*(2-Y)+u) := by simp [Apoly] <;> ring <;> simp
    have h2Y : 0 < 2-Y := by linarith
    rw [he]
    positivity
  have ha3 : 0 < Apoly X Y (1+u) 3 := by
    have he : Apoly X Y (1+u) 3 = X*(Y*(2-X)+u) := by simp [Apoly] <;> ring <;> simp
    have h2X : 0 < 2-X := by linarith
    rw [he]
    positivity
  exact ⟨ha0, ha1, ha2, ha3⟩

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_s_ne_one (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hP : P4poly X Y s < 0) : s ≠ 1 := by
  intro hs
  subst s
  have h1X : 0 < 1-X := by linarith
  have h1Y : 0 < 1-Y := by linarith
  have hp : 0 < X*Y*(4+4*(1-X)+4*(1-Y)+X*Y) := by positivity
  have he : P4poly X Y 1 = X*Y*(4+4*(1-X)+4*(1-Y)+X*Y) := by
    unfold P4poly
    ring
  linarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_ne_diagonal (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hP : P4poly X Y s < 0)
    (hs1 : s < 1) : X ≠ Y := by
  intro heq
  subst X
  let t := 1-s
  have ht : 0 < t := by dsimp [t]; linarith
  have hd : 0 < 2*Y+t := by positivity
  have heH : Hpoly Y Y s = (Y*(2-Y)-t)*(2*Y+t) := by
    dsimp [t]
    unfold Hpoly
    ring
  have hmul : 0 < (Y*(2-Y)-t)*(2*Y+t) := by rwa [heH] at hH
  have hT : 0 < Y*(2-Y)-t := (mul_pos_iff_of_pos_right hd).mp hmul
  have h6 : 0 < 6-Y := by linarith
  have hc : 0 < Y*(6-Y)+3*t := by positivity
  have hp : 0 < (Y*(2-Y)-t)*(Y*(6-Y)+3*t) := mul_pos hT hc
  have heP : P4poly Y Y s = (Y*(2-Y)-t)*(Y*(6-Y)+3*t) := by
    dsimp [t]
    unfold P4poly
    ring
  linarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_regions (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0) :
    (s < 1 ∧ Y < X) ∨ (s < 1 ∧ X < Y) ∨ 1 < s := by
  have hsne := S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_s_ne_one X Y s hX0 hX1 hY0 hY1 hP
  rcases lt_or_gt_of_ne hsne with hs | hs
  · have hxyne := S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_near_ne_diagonal X Y s hX0 hX1 hY0 hY1 hH hP hs
    rcases lt_or_gt_of_ne hxyne with hxy | hyx
    · exact Or.inr (Or.inl ⟨hs,hxy⟩)
    · exact Or.inl ⟨hs,hyx⟩
  · exact Or.inr (Or.inr hs)

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_exactly_one (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0) :
    ∃! k : Fin 3, ![s < 1 ∧ Y < X, s < 1 ∧ X < Y, 1 < s] k := by
  rcases S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_regions X Y s hX0 hX1 hY0 hY1 hH hs0 hP with h | h | h
  · refine ⟨0, by simpa using h, ?_⟩
    intro k hk
    fin_cases k
    · rfl
    · have hk' : s < 1 ∧ X < Y := by simpa using hk
      exfalso
      linarith [hk'.2,h.2]
    · have hk' : 1 < s := by simpa using hk
      exfalso
      linarith [hk',h.1]
  · refine ⟨1, by simpa using h, ?_⟩
    intro k hk
    fin_cases k
    · have hk' : s < 1 ∧ Y < X := by simpa using hk
      exfalso
      linarith [hk'.2,h.2]
    · rfl
    · have hk' : 1 < s := by simpa using hk
      exfalso
      linarith [hk',h.1]
  · refine ⟨2, by simpa using h, ?_⟩
    intro k hk
    fin_cases k
    · have hk' : s < 1 ∧ Y < X := by simpa using hk
      exfalso
      linarith [hk'.1,h]
    · have hk' : s < 1 ∧ X < Y := by simpa using hk
      exfalso
      linarith [hk'.1,h]
    · rfl

end

section

private def S5b_HardSphereB5_Lean_Geometry_PathCore_SliverCountTable (c : Fin 4 → Pt) (X Y s : ℝ) : Prop :=
  ((s < 1 ∧ Y < X) → nRet c = ![0, 2, 0, 2]) ∧
  ((s < 1 ∧ X < Y) → nRet c = ![2, 0, 2, 0]) ∧
  (1 < s → nRet c = ![2, 2, 0, 0])

private def S5b_HardSphereB5_Lean_Geometry_PathCore_SliverCommonTable (c : Fin 4 → Pt) (X Y s : ℝ) : Prop :=
  ((s < 1 ∧ Y < X) → ∀ i j : Fin 4, i ≠ j →
    (isCommon c i j ↔ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0))) ∧
  ((s < 1 ∧ X < Y) → ∀ i j : Fin 4, i ≠ j →
    (isCommon c i j ↔ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) ∧
  (1 < s → ∀ i j : Fin 4, i ≠ j →
    (isCommon c i j ↔ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)))

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_common02_of_count_table (c : Fin 4 → Pt)
    (ht : nRet c = ![0, 2, 0, 2]) :
    ∀ i j : Fin 4, i ≠ j →
      (isCommon c i j ↔ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) := by
  intro i j hij
  unfold isCommon
  rw [ht]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_common13_of_count_table (c : Fin 4 → Pt)
    (ht : nRet c = ![2, 0, 2, 0]) :
    ∀ i j : Fin 4, i ≠ j →
      (isCommon c i j ↔ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) := by
  intro i j hij
  unfold isCommon
  rw [ht]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_common23_of_count_table (c : Fin 4 → Pt)
    (ht : nRet c = ![2, 2, 0, 0]) :
    ∀ i j : Fin 4, i ≠ j →
      (isCommon c i j ↔ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
  intro i j hij
  unfold isCommon
  rw [ht]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_table_of_selector (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_SliverCountTable c X Y s ∧ S5b_HardSphereB5_Lean_Geometry_PathCore_SliverCommonTable c X Y s := by
  have ht0 (hr : s < 1 ∧ Y < X) : nRet c = ![0, 2, 0, 2] := by
    rcases S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_signs_near_gt X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
      hc.H_pos hs0 hP hr.1 hr.2 with ⟨ha0,ha1,ha2,ha3⟩
    have hn0 : ¬ Apoly X Y s 0 < 0 := not_lt.mpr ha0.le
    have hn2 : ¬ Apoly X Y s 2 < 0 := not_lt.mpr ha2.le
    funext l
    fin_cases l <;> simp [hSel, hn0,ha1,hn2,ha3]
  have ht1 (hr : s < 1 ∧ X < Y) : nRet c = ![2, 0, 2, 0] := by
    rcases S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_signs_near_lt X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
      hc.H_pos hs0 hP hr.1 hr.2 with ⟨ha0,ha1,ha2,ha3⟩
    have hn1 : ¬ Apoly X Y s 1 < 0 := not_lt.mpr ha1.le
    have hn3 : ¬ Apoly X Y s 3 < 0 := not_lt.mpr ha3.le
    funext l
    fin_cases l <;> simp [hSel, ha0,hn1,ha2,hn3]
  have ht2 (hr : 1 < s) : nRet c = ![2, 2, 0, 0] := by
    rcases S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_signs_far X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
      hc.H_pos hs0 hP hr with ⟨ha0,ha1,ha2,ha3⟩
    have hn2 : ¬ Apoly X Y s 2 < 0 := not_lt.mpr ha2.le
    have hn3 : ¬ Apoly X Y s 3 < 0 := not_lt.mpr ha3.le
    funext l
    fin_cases l <;> simp [hSel, ha0,ha1,hn2,hn3]
  refine ⟨⟨ht0,ht1,ht2⟩, ?_⟩
  exact ⟨fun hr => S5b_HardSphereB5_Lean_Geometry_PathCore_common02_of_count_table c (ht0 hr),
    fun hr => S5b_HardSphereB5_Lean_Geometry_PathCore_common13_of_count_table c (ht1 hr),
    fun hr => S5b_HardSphereB5_Lean_Geometry_PathCore_common23_of_count_table c (ht2 hr)⟩

private def S5b_HardSphereB5_Lean_Geometry_PathCore_SliverIncidenceLedger (c : Fin 4 → Pt) : Prop :=
  (∑ l : Fin 4, nRet c l) = 4 ∧
  ∃ i j : Fin 4, i ≠ j ∧ isCommon c i j ∧
    (∀ a b : Fin 4, a ≠ b →
      (isCommon c a b ↔ (a = i ∧ b = j) ∨ (a = j ∧ b = i))) ∧
    (∀ a : Fin 4, (∑ l ∈ (Finset.univ : Finset (Fin 4)).erase a, nRet c l) =
      if a = i ∨ a = j then 4 else 2)

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence_of_count_table (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hTable : S5b_HardSphereB5_Lean_Geometry_PathCore_SliverCountTable c X Y s) : S5b_HardSphereB5_Lean_Geometry_PathCore_SliverIncidenceLedger c := by
  rcases hTable with ⟨ht0,ht1,ht2⟩
  rcases S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_regions X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
    hc.H_pos hs0 hP with hr | hr | hr
  · have ht := ht0 hr
    have hcom := S5b_HardSphereB5_Lean_Geometry_PathCore_common02_of_count_table c ht
    refine ⟨?_,0,2,by decide,?_,hcom,?_⟩
    · rw [ht]
      decide
    · exact (hcom 0 2 (by decide)).mpr (by simp)
    · intro a
      rw [ht]
      fin_cases a <;> decide
  · have ht := ht1 hr
    have hcom := S5b_HardSphereB5_Lean_Geometry_PathCore_common13_of_count_table c ht
    refine ⟨?_,1,3,by decide,?_,hcom,?_⟩
    · rw [ht]
      decide
    · exact (hcom 1 3 (by decide)).mpr (by simp)
    · intro a
      rw [ht]
      fin_cases a <;> decide
  · have ht := ht2 hr
    have hcom := S5b_HardSphereB5_Lean_Geometry_PathCore_common23_of_count_table c ht
    refine ⟨?_,2,3,by decide,?_,hcom,?_⟩
    · rw [ht]
      decide
    · exact (hcom 2 3 (by decide)).mpr (by simp)
    · intro a
      rw [ht]
      fin_cases a <;> decide

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence_of_selector (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0) :
    S5b_HardSphereB5_Lean_Geometry_PathCore_SliverIncidenceLedger c :=
  S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence_of_count_table c X Y s hc hs0 hP
    (S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_table_of_selector c X Y s hc hs0 hP hSel).1

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_lemma64d_of_incidence (c : Fin 4 → Pt) (X Y s Bminus : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hs1 : s < 1)
    (hPne : P4poly X Y s ≠ 0)
    (hBulk : 0 < P4poly X Y s → ∀ l, nRet c l = 1)
    (hTable : P4poly X Y s < 0 → S5b_HardSphereB5_Lean_Geometry_PathCore_SliverCountTable c X Y s)
    (hBulkIff : 0 < P4poly X Y s ↔ Bminus < X)
    (hNearGt : P4poly X Y s < 0 → (Y < X ↔ s < (1-Y)^2))
    (hNearLt : P4poly X Y s < 0 → (X < Y ↔ (1-Y)^2 < s)) :
    (Bminus < X → nRet c 1 = 1 ∧ nRet c 0 = 1) ∧
    (X < Bminus ∧ s < (1-Y)^2 → nRet c 1 = 2 ∧ nRet c 0 = 0) ∧
    (X < Bminus ∧ (1-Y)^2 < s → nRet c 1 = 0 ∧ nRet c 0 = 2) := by
  have hsl (hx : X < Bminus) : P4poly X Y s < 0 := by
    have hn : ¬ 0 < P4poly X Y s := by
      intro hp
      have hb := hBulkIff.mp hp
      linarith
    exact lt_of_le_of_ne (le_of_not_gt hn) hPne
  refine ⟨?_,?_,?_⟩
  · intro hx
    have hb := hBulk (hBulkIff.mpr hx)
    exact ⟨hb 1,hb 0⟩
  · intro hr
    have hp := hsl hr.1
    have hyx : Y < X := (hNearGt hp).mpr hr.2
    have ht := (hTable hp).1 ⟨hs1,hyx⟩
    constructor
    · simpa using congrFun ht (1 : Fin 4)
    · simpa using congrFun ht (0 : Fin 4)
  · intro hr
    have hp := hsl hr.1
    have hxy : X < Y := (hNearLt hp).mpr hr.2
    have ht := (hTable hp).2.1 ⟨hs1,hxy⟩
    constructor
    · simpa using congrFun ht (1 : Fin 4)
    · simpa using congrFun ht (0 : Fin 4)

end

section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_selector {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) :
    ∀ l, nRet c l = if 0 < Qpoly X Y s l ∧ Apoly X Y s l < 0 then 2 else 0 := by
  intro l
  rw [S5b_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l,
    if_neg (not_lt_of_ge (le_of_lt hP))]
  simp only [S5b_HardSphereB5_Lean_Geometry_PathCore_path_Qpoly_pos c X Y s hc l, true_and]
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence_of_deps {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) :
    (∀ l, nRet c l = if 0 < Qpoly X Y s l ∧ Apoly X Y s l < 0 then 2 else 0) ∧
      ∑ l, nRet c l = 4 ∧
      ∃ i j, i ≠ j ∧ isCommon c i j ∧
        ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = if m = i ∨ m = j then 4 else 2 := by
  have hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0 := by
    intro l
    rw [S5b_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l,
      if_neg (not_lt_of_ge (le_of_lt hP))]
  have hledger := S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence_of_selector c X Y s hc (S5b_HardSphereB5_Lean_Geometry_PathCore_path_s_pos c X Y s hc) hP hSel
  obtain ⟨hsum,i,j,hij,hcommon,hunique,hcounts⟩ := hledger
  exact ⟨S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_selector hc hP,hsum,i,j,hij,hcommon,hcounts⟩
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) :
    (∀ l, nRet c l = if 0 < Qpoly X Y s l ∧ Apoly X Y s l < 0 then 2 else 0) ∧
      ∑ l, nRet c l = 4 ∧
      ∃ i j, i ≠ j ∧ isCommon c i j ∧
        ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = if m = i ∨ m = j then 4 else 2 := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence_of_deps c X Y s hc hP

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
