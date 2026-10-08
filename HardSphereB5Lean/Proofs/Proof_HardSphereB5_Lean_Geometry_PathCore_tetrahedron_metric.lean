import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

noncomputable section
open MeasureTheory Real

open HardSphereB5.Lean.Geometry.PathCore

open HardSphereB5.Lean (Pt)
open scoped Classical

open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000

private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq (x : Pt) : ℝ := ⟪x, x⟫
open HardSphereB5.Lean.Geometry.PathCore.TripleGeometry
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.faceDelta (v w : Pt) : ℝ := DeltaT (sq v) (sq w) (sq (v - w))
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.faceQ (v w : Pt) : ℝ := QT (sq v) (sq w) (sq (v - w))
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.center (v w : Pt) : Pt :=
  (sq w * (sq v - sq w + sq (v - w)) / faceDelta v w) • v +
  (sq v * (sq w - sq v + sq (v - w)) / faceDelta v w) • w
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.height (v w : Pt) : ℝ := Real.sqrt (faceQ v w / faceDelta v w)
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.orientedNormal (v w z : Pt) : Pt :=
  if 0 < ⟪z, cross v w⟫ then ‖cross v w‖⁻¹ • cross v w
  else -(‖cross v w‖⁻¹ • cross v w)
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.triple (v w : Pt) : Set Pt := {x | ‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1}
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.fourthThreshold (v w z : Pt) : ℝ :=
  (sq z - 2 * ⟪z, center v w⟫) / (2 * ⟪z, orientedNormal v w z⟫)

private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq_eq_norm_sq (x : Pt) : sq x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq_nonneg (x : Pt) : 0 ≤ sq x := by rw [sq_eq_norm_sq]; positivity
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq_sub (x y : Pt) : sq (x - y) = sq x + sq y - 2 * ⟪x, y⟫ := by
  simp only [sq, inner_sub_left, inner_sub_right, real_inner_comm y x]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq_eq_one_iff (x : Pt) : sq x = 1 ↔ ‖x‖ = 1 := by
  rw [sq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg x]
  · intro h; rw [h]; norm_num
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.inner_coords (x y : Pt) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1,
      v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := by
  simp [cross, SphereGeom.cross, cross_apply]
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.cross_v (v w : Pt) : ⟪v, cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.cross_w (v w : Pt) : ⟪w, cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.cross_sq (v w : Pt) :
    sq (cross v w) = sq v * sq w - ⟪v, w⟫ ^ 2 := by
  simp only [sq, inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.gram_resolution (v w x : Pt) :
    (sq v * sq w - ⟪v, w⟫ ^ 2) • x =
      (sq w * ⟪v, x⟫ - ⟪v, w⟫ * ⟪w, x⟫) • v +
      (sq v * ⟪w, x⟫ - ⟪v, w⟫ * ⟪v, x⟫) • w +
      ⟪cross v w, x⟫ • cross v w := by
  simp only [sq, inner_coords]
  ext i
  fin_cases i <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.delta_gram (v w : Pt) :
    faceDelta v w = 4 * (sq v * sq w - ⟪v, w⟫ ^ 2) := by
  simp only [faceDelta, DeltaT, sq_sub]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.q_delta (v w : Pt) :
    faceQ v w = faceDelta v w - sq v * sq w * sq (v - w) := rfl

private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.center_inner_v (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, v⟫ = sq v / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq, real_inner_comm w v]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.center_inner_w (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, w⟫ = sq w / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.center_sq (v w : Pt) (hD : faceDelta v w ≠ 0) :
    sq (center v w) = sq v * sq w * sq (v - w) / faceDelta v w := by
  change ⟪center v w, center v w⟫ = _
  nth_rw 2 [center]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    center_inner_v v w hD, center_inner_w v w hD]
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.cross_norm_pos (v w : Pt) (hD : 0 < faceDelta v w) : 0 < ‖cross v w‖ := by
  have he := delta_gram v w
  have hs := cross_sq v w
  rw [sq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cross v w)]
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.unit_cross_norm (v w : Pt) (hD : 0 < faceDelta v w) :
    ‖‖cross v w‖⁻¹ • cross v w‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cross_norm_pos v w hD))]
  exact inv_mul_cancel₀ (ne_of_gt (cross_norm_pos v w hD))
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.normal_norm (v w z : Pt) (hD : 0 < faceDelta v w) :
    ‖orientedNormal v w z‖ = 1 := by
  unfold orientedNormal
  split_ifs <;> simp only [norm_neg, unit_cross_norm v w hD]
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.normal_sq (v w z : Pt) (hD : 0 < faceDelta v w) :
    sq (orientedNormal v w z) = 1 := by
  rw [sq_eq_norm_sq, normal_norm v w z hD]; norm_num
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.normal_v (v w z : Pt) : ⟪v, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_v]
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.normal_w (v w z : Pt) : ⟪w, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_w]
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.normal_oriented (v w z : Pt) (hD : 0 < faceDelta v w)
    (hG : ⟪z, cross v w⟫ ≠ 0) : 0 < ⟪z, orientedNormal v w z⟫ := by
  have hi := inv_pos.mpr (cross_norm_pos v w hD)
  unfold orientedNormal
  split_ifs with hz
  · rw [real_inner_smul_right]; exact mul_pos hi hz
  · rw [inner_neg_right, real_inner_smul_right]
    have hz' : ⟪z, cross v w⟫ < 0 := lt_of_le_of_ne (le_of_not_gt hz) hG
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hi hz')
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.center_normal (v w z : Pt) : ⟪center v w, orientedNormal v w z⟫ = 0 := by
  simp only [center, inner_add_left, real_inner_smul_left, normal_v, normal_w,
    mul_zero, add_zero]

private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.perp_as_normal (v w z d : Pt) (hD : 0 < faceDelta v w)
    (hv : ⟪v, d⟫ = 0) (hw : ⟪w, d⟫ = 0) :
    d = ⟪orientedNormal v w z, d⟫ • orientedNormal v w z := by
  have hn := ne_of_gt (cross_norm_pos v w hD)
  have hsn : sq (cross v w) ≠ 0 := by
    rw [sq_eq_norm_sq]; exact pow_ne_zero 2 hn
  have hr := gram_resolution v w d
  rw [← cross_sq, hv, hw] at hr
  simp only [mul_zero, sub_self, zero_smul, zero_add] at hr
  have hd : d = (⟪cross v w, d⟫ / sq (cross v w)) • cross v w := by
    calc
      d = (sq (cross v w))⁻¹ • (sq (cross v w) • d) := by
        rw [smul_smul, inv_mul_cancel₀ hsn, one_smul]
      _ = (⟪cross v w, d⟫ / sq (cross v w)) • cross v w := by
        rw [hr, smul_smul]; congr 1; ring
  have hc : d = ⟪‖cross v w‖⁻¹ • cross v w, d⟫ • (‖cross v w‖⁻¹ • cross v w) := by
    calc
      d = (⟪cross v w, d⟫ / sq (cross v w)) • cross v w := hd
      _ = ⟪‖cross v w‖⁻¹ • cross v w, d⟫ • (‖cross v w‖⁻¹ • cross v w) := by
        rw [real_inner_smul_left, smul_smul]
        congr 1
        rw [sq_eq_norm_sq]
        field_simp [hn]
  unfold orientedNormal
  split_ifs
  · exact hc
  · simpa only [inner_neg_left, neg_smul, smul_neg, neg_neg] using hc

private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.height_pos (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    0 < height v w := Real.sqrt_pos.mpr (div_pos hQ hD)
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.center_height (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    sq (center v w) + height v w ^ 2 = 1 := by
  rw [center_sq v w (ne_of_gt hD)]
  unfold height
  rw [Real.sq_sqrt (le_of_lt (div_pos hQ hD)), q_delta]
  field_simp [ne_of_gt hD]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.mem_triple_iff (v w x : Pt) :
    x ∈ triple v w ↔ sq x = 1 ∧ ⟪x, v⟫ = sq v / 2 ∧ ⟪x, w⟫ = sq w / 2 := by
  change (‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1) ↔ _
  simp only [← sq_eq_one_iff, sq_sub]
  constructor
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.center_line_sq (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w) :
    sq (center v w + r • orientedNormal v w z) = sq (center v w) + r ^ 2 := by
  have ho := center_normal v w z
  have hn : ⟪orientedNormal v w z, orientedNormal v w z⟫ = 1 := normal_sq v w z hD
  have ho' : ⟪orientedNormal v w z, center v w⟫ = 0 := (real_inner_comm (center v w) _).trans ho
  simp only [sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ho, ho', hn]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.line_mem_triple (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hr : r ^ 2 = height v w ^ 2) :
    center v w + r • orientedNormal v w z ∈ triple v w := by
  rw [mem_triple_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [center_line_sq v w z r hD, hr]
    exact center_height v w hD hQ
  · rw [inner_add_left, real_inner_smul_left, real_inner_comm v (orientedNormal v w z),
      normal_v, mul_zero, add_zero]
    exact center_inner_v v w (ne_of_gt hD)
  · rw [inner_add_left, real_inner_smul_left, real_inner_comm w (orientedNormal v w z),
      normal_w, mul_zero, add_zero]
    exact center_inner_w v w (ne_of_gt hD)

private theorem HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.triple_exact (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    triple v w = {center v w + height v w • orientedNormal v w z,
      center v w - height v w • orientedNormal v w z} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    obtain ⟨hs, hv, hw⟩ := (mem_triple_iff v w x).mp hx
    have hvd : ⟪v, x - center v w⟫ = 0 := by
      rw [inner_sub_right, real_inner_comm x v, real_inner_comm (center v w) v, hv,
        center_inner_v v w (ne_of_gt hD)]
      ring
    have hwd : ⟪w, x - center v w⟫ = 0 := by
      rw [inner_sub_right, real_inner_comm x w, real_inner_comm (center v w) w, hw,
        center_inner_w v w (ne_of_gt hD)]
      ring
    let r := ⟪orientedNormal v w z, x - center v w⟫
    have hd := perp_as_normal v w z (x - center v w) hD hvd hwd
    have hxline : x = center v w + r • orientedNormal v w z := by
      calc x = center v w + (x - center v w) := by abel
           _ = center v w + r • orientedNormal v w z := by rw [hd]
    have hr : r ^ 2 = height v w ^ 2 := by
      rw [hxline, center_line_sq v w z r hD] at hs
      linarith [center_height v w hD hQ]
    have hf : (r - height v w) * (r + height v w) = 0 := by nlinarith [hr]
    rcases mul_eq_zero.mp hf with hp | hm
    · left; have he : r = height v w := by linarith
      simpa only [he] using hxline
    · right; have he : r = -height v w := by linarith
      simpa only [he, neg_smul, sub_eq_add_neg] using hxline
  · rintro (hx | hx)
    · rw [hx]; exact line_mem_triple v w z (height v w) hD hQ rfl
    · rw [hx, sub_eq_add_neg, ← neg_smul]
      exact line_mem_triple v w z (-height v w) hD hQ (neg_sq _)

private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z) ^ 2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z) ^ 2 -
      inner ℝ w w * (inner ℝ v z) ^ 2 -
      inner ℝ z z * (inner ℝ v w) ^ 2 := by
  change ⟪cross v w, z⟫ ^ 2 = _
  simp only [inner_coords, cross_coords]
  simp
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.triple_points_ne (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    center v w + height v w • orientedNormal v w z ≠
      center v w - height v w • orientedNormal v w z := by
  intro he
  have hh := height_pos v w hD hQ
  have hs : ⟪orientedNormal v w z, orientedNormal v w z⟫ = 1 := normal_sq v w z hD
  have hn0 : ⟪orientedNormal v w z, center v w⟫ = 0 :=
    (real_inner_comm (center v w) _).trans (center_normal v w z)
  have hi := congrArg (fun x : Pt => ⟪orientedNormal v w z, x⟫) he
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hs, hn0] at hi
  linarith

private theorem HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.fourth_sq_formula (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hr : r ^ 2 = height v w ^ 2) :
    ‖center v w + r • orientedNormal v w z - z‖ ^ 2 - 1 =
      sq z - 2 * ⟪z, center v w⟫ - 2 * r * ⟪z, orientedNormal v w z⟫ := by
  rw [← sq_eq_norm_sq, sq_sub, center_line_sq v w z r hD,
    inner_add_left, real_inner_smul_left, real_inner_comm z (center v w),
    real_inner_comm z (orientedNormal v w z), hr]
  linarith [center_height v w hD hQ]

private theorem HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.fourth_mem_iff (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hG : ⟪z, cross v w⟫ ≠ 0)
    (hr : r ^ 2 = height v w ^ 2) :
    center v w + r • orientedNormal v w z ∈ Metric.closedBall z 1 ↔
      fourthThreshold v w z ≤ r := by
  have hd : 0 < 2 * ⟪z, orientedNormal v w z⟫ :=
    mul_pos (by norm_num) (normal_oriented v w z hD hG)
  have hf := fourth_sq_formula v w z r hD hQ hr
  rw [Metric.mem_closedBall, dist_eq_norm, fourthThreshold, div_le_iff₀ hd]
  have hn := norm_nonneg (center v w + r • orientedNormal v w z - z)
  constructor <;> intro h <;> nlinarith

private theorem HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.oriented_triple_bridge (v w z : Pt) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hG : ⟪z, cross v w⟫ ≠ 0) :
    ‖orientedNormal v w z‖ = 1 ∧
      ⟪v, orientedNormal v w z⟫ = 0 ∧ ⟪w, orientedNormal v w z⟫ = 0 ∧
      0 < ⟪z, orientedNormal v w z⟫ ∧
      triple v w = {center v w + height v w • orientedNormal v w z,
        center v w - height v w • orientedNormal v w z} :=
  ⟨normal_norm v w z hD, normal_v v w z, normal_w v w z,
    normal_oriented v w z hD hG, triple_exact v w z hD hQ⟩

end

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private lemma HardSphereB5.Lean.Geometry.PathCore.q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

private lemma HardSphereB5.Lean.Geometry.PathCore.q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]

private lemma HardSphereB5.Lean.Geometry.PathCore.inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith

private def HardSphereB5.Lean.Geometry.PathCore.Dpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![DeltaT X 1 s, DeltaT 1 Y s, DeltaT 1 Y 1, DeltaT 1 1 X]

private def HardSphereB5.Lean.Geometry.PathCore.gramPoly (a b cc d e f : ℝ) : ℝ :=
  4*a*b*d + (a+b-cc)*(a+d-e)*(b+d-f)
    - a*(b+d-f)^2 - b*(a+d-e)^2 - d*(a+b-cc)^2

private def HardSphereB5.Lean.Geometry.PathCore.faceAPoly (a b cc d e f : ℝ) : ℝ :=
  DeltaT a b cc * d - b*(a-b+cc)*(a+d-e) - a*(b-a+cc)*(b+d-f)

private lemma HardSphereB5.Lean.Geometry.PathCore.face_polys (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
    let i := (faceVerts l).1
    let j := (faceVerts l).2.1
    let k := (faceVerts l).2.2
    Qface c l = Qpoly X Y s l ∧
    Deltaf c i j k = Dpoly X Y s l ∧
    faceAPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) = Apoly X Y s l ∧
    gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) = Hpoly X Y s := by
  have h10 : q c 1 0 = 1 := by rw [q_symm', hc.q01]
  have h20 : q c 2 0 = 1 := by rw [q_symm', hc.q02]
  have h30 : q c 3 0 = Y := by rw [q_symm', hc.q03]
  have h21 : q c 2 1 = X := by rw [q_symm', hc.q12]
  have h31 : q c 3 1 = 1 := by rw [q_symm', hc.q13]
  have h32 : q c 3 2 = s := by rw [q_symm', hc.q23]
  fin_cases l <;>
    dsimp [faceVerts, Qface, Qf, Deltaf, QT, DeltaT, Dpoly, Qpoly, Apoly,
      faceAPoly, gramPoly, Hpoly] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hc.q01, hc.q02, hc.q03, hc.q12, hc.q13, hc.q23,
      h10, h20, h30, h21, h31, h32] <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.cayley_menger_face_identity (X Y s : ℝ) (l : Fin 4) :
    Apoly X Y s l ^ 2 - 4 * Hpoly X Y s * Qpoly X Y s l =
      -Dpoly X Y s l * P4poly X Y s := by
  fin_cases l <;> simp [Apoly, Hpoly, Qpoly, Dpoly, DeltaT, P4poly] <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z)^2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z)^2 -
      inner ℝ w w * (inner ℝ v z)^2 -
      inner ℝ z z * (inner ℝ v w)^2 :=
  TripleGeometry.cross_gram_identity v w z

private lemma HardSphereB5.Lean.Geometry.PathCore.gram_from_q (c : Fin 4 → Pt) (i j k l : Fin 4) :
    4 * (inner ℝ (SphereGeom.cross (c j - c i) (c k - c i)) (c l - c i))^2 =
    gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) := by
  rw [cross_gram_identity, ← q_inner, ← q_inner, ← q_inner,
    inner_from_q, inner_from_q, inner_from_q]
  simp only [gramPoly]
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.face_det_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
    0 < (inner ℝ (SphereGeom.cross
      (c (faceVerts l).2.1 - c (faceVerts l).1)
      (c (faceVerts l).2.2 - c (faceVerts l).1)) (c l - c (faceVerts l).1))^2 := by
  have hg := gram_from_q c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 l
  rw [(face_polys c X Y s hc l).2.2.2] at hg
  linarith [hc.H_pos]

private lemma HardSphereB5.Lean.Geometry.PathCore.retained_set_eq (c : Fin 4 → Pt) (l : Fin 4) :
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

private lemma HardSphereB5.Lean.Geometry.PathCore.bulk_patch_counts (c : Fin 4 → Pt) (hn : ∀ l, nRet c l = 1) :
    ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 := by
  intro m
  simp_rw [hn]
  simp

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
private lemma HardSphereB5.Lean.Geometry.PathCore.q_nonneg' (c : Fin 4 → Pt) (i j : Fin 4) : 0 ≤ q c i j := by unfold q; positivity

private lemma HardSphereB5.Lean.Geometry.PathCore.path_s_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) : 0 < s := by
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

private lemma HardSphereB5.Lean.Geometry.PathCore.path_Qpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) :
    ∀ l, 0 < Qpoly X Y s l := by
  have hs := path_s_pos c X Y s hc
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

private lemma HardSphereB5.Lean.Geometry.PathCore.path_Dpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
    0 < Dpoly X Y s l := by
  have hQ : 0 < Qface c l := by rw [(face_polys c X Y s hc l).1]; exact path_Qpoly_pos c X Y s hc l
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  have hd := (face_polys c X Y s hc l).2.1
  change Deltaf c i j k = Dpoly X Y s l at hd
  have hn : 0 ≤ q c i j * q c i k * q c j k :=
    mul_nonneg (mul_nonneg (q_nonneg' c i j) (q_nonneg' c i k)) (q_nonneg' c j k)
  change 0 < Deltaf c i j k - q c i j*q c i k*q c j k at hQ
  linarith

set_option maxHeartbeats 2200000

variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.s3_q_symm (i j : Fin 4) : q c i j=q c j i := by simp [q,dist_comm]

private lemma HardSphereB5.Lean.Geometry.PathCore.s3_face_delta_pos (hc : IsPathConfig c X Y s) (i j k : Fin 4)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) : 0<Deltaf c i j k := by
  have h0 := path_Dpoly_pos c X Y s hc 0
  have h1 := path_Dpoly_pos c X Y s hc 1
  have h2 := path_Dpoly_pos c X Y s hc 2
  have h3 := path_Dpoly_pos c X Y s hc 3
  change 0 < DeltaT X 1 s at h0
  change 0 < DeltaT 1 Y s at h1
  change 0 < DeltaT 1 Y 1 at h2
  change 0 < DeltaT 1 1 X at h3
  simp only [DeltaT] at h0 h1 h2 h3
  have h01 : q c ⟨0,by decide⟩ ⟨1,by decide⟩=1 := hc.q01
  have h02 : q c ⟨0,by decide⟩ ⟨2,by decide⟩=1 := hc.q02
  have h03 : q c ⟨0,by decide⟩ ⟨3,by decide⟩=Y := hc.q03
  have h12 : q c ⟨1,by decide⟩ ⟨2,by decide⟩=X := hc.q12
  have h13 : q c ⟨1,by decide⟩ ⟨3,by decide⟩=1 := hc.q13
  have h23 : q c ⟨2,by decide⟩ ⟨3,by decide⟩=s := hc.q23
  have h10 : q c ⟨1,by decide⟩ ⟨0,by decide⟩=1 := (s3_q_symm 1 0).trans hc.q01
  have h20 : q c ⟨2,by decide⟩ ⟨0,by decide⟩=1 := (s3_q_symm 2 0).trans hc.q02
  have h30 : q c ⟨3,by decide⟩ ⟨0,by decide⟩=Y := (s3_q_symm 3 0).trans hc.q03
  have h21 : q c ⟨2,by decide⟩ ⟨1,by decide⟩=X := (s3_q_symm 2 1).trans hc.q12
  have h31 : q c ⟨3,by decide⟩ ⟨1,by decide⟩=1 := (s3_q_symm 3 1).trans hc.q13
  have h32 : q c ⟨3,by decide⟩ ⟨2,by decide⟩=s := (s3_q_symm 3 2).trans hc.q23
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim
  all_goals norm_num only [Fin.reduceFinMk]
  all_goals simp only [Deltaf,DeltaT,h01,h02,h03,h12,h13,h23,
    h10,h20,h30,h21,h31,h32]
  all_goals nlinarith [h0,h1,h2,h3]

private lemma HardSphereB5.Lean.Geometry.PathCore.s3_face_Q_pos (hc : IsPathConfig c X Y s) (i j k : Fin 4)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) : 0<Qf c i j k := by
  have h0 := path_Qpoly_pos c X Y s hc 0
  have h1 := path_Qpoly_pos c X Y s hc 1
  have h2 := path_Qpoly_pos c X Y s hc 2
  have h3 := path_Qpoly_pos c X Y s hc 3
  change 0 < -X^2+X*s+2*X-s^2+2*s-1 at h0
  change 0 < -Y^2+Y*s+2*Y-s^2+2*s-1 at h1
  change 0 < Y*(3-Y) at h2
  change 0 < X*(3-X) at h3
  have h01 : q c ⟨0,by decide⟩ ⟨1,by decide⟩=1 := hc.q01
  have h02 : q c ⟨0,by decide⟩ ⟨2,by decide⟩=1 := hc.q02
  have h03 : q c ⟨0,by decide⟩ ⟨3,by decide⟩=Y := hc.q03
  have h12 : q c ⟨1,by decide⟩ ⟨2,by decide⟩=X := hc.q12
  have h13 : q c ⟨1,by decide⟩ ⟨3,by decide⟩=1 := hc.q13
  have h23 : q c ⟨2,by decide⟩ ⟨3,by decide⟩=s := hc.q23
  have h10 : q c ⟨1,by decide⟩ ⟨0,by decide⟩=1 := (s3_q_symm 1 0).trans hc.q01
  have h20 : q c ⟨2,by decide⟩ ⟨0,by decide⟩=1 := (s3_q_symm 2 0).trans hc.q02
  have h30 : q c ⟨3,by decide⟩ ⟨0,by decide⟩=Y := (s3_q_symm 3 0).trans hc.q03
  have h21 : q c ⟨2,by decide⟩ ⟨1,by decide⟩=X := (s3_q_symm 2 1).trans hc.q12
  have h31 : q c ⟨3,by decide⟩ ⟨1,by decide⟩=1 := (s3_q_symm 3 1).trans hc.q13
  have h32 : q c ⟨3,by decide⟩ ⟨2,by decide⟩=s := (s3_q_symm 3 2).trans hc.q23
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim
  all_goals norm_num only [Fin.reduceFinMk]
  all_goals simp only [Qf,QT,DeltaT,h01,h02,h03,h12,h13,h23,
    h10,h20,h30,h21,h31,h32]
  all_goals nlinarith [h0,h1,h2,h3]

private lemma HardSphereB5.Lean.Geometry.PathCore.s3_TG_center (i j k : Fin 4) :
    faceCircRel c i j k=TripleGeometry.center (c j-c i) (c k-c i) := by
  have huv : TripleGeometry.sq ((c j-c i)-(c k-c i))=q c j k := by
    rw [TripleGeometry.sq_eq_norm_sq]
    have hv : (c j-c i)-(c k-c i)=c j-c k := by abel
    rw [hv]
    simp [q,dist_eq_norm]
  have hv : TripleGeometry.sq (c j-c i)=q c i j := by
    rw [TripleGeometry.sq_eq_norm_sq]
    simp only [q,dist_eq_norm,norm_sub_rev]
  have hw : TripleGeometry.sq (c k-c i)=q c i k := by
    rw [TripleGeometry.sq_eq_norm_sq]
    simp only [q,dist_eq_norm,norm_sub_rev]
  simp only [faceCircRel,TripleGeometry.center,TripleGeometry.faceDelta,hv,hw,huv,Deltaf]

private lemma HardSphereB5.Lean.Geometry.PathCore.s3_TG_delta (i j k : Fin 4) :
    TripleGeometry.faceDelta (c j-c i) (c k-c i)=Deltaf c i j k := by
  have huv : TripleGeometry.sq ((c j-c i)-(c k-c i))=q c j k := by
    rw [TripleGeometry.sq_eq_norm_sq]
    have hv : (c j-c i)-(c k-c i)=c j-c k := by abel
    rw [hv]; simp [q,dist_eq_norm]
  have hv : TripleGeometry.sq (c j-c i)=q c i j := by
    rw [TripleGeometry.sq_eq_norm_sq];simp only [q,dist_eq_norm,norm_sub_rev]
  have hw : TripleGeometry.sq (c k-c i)=q c i k := by
    rw [TripleGeometry.sq_eq_norm_sq];simp only [q,dist_eq_norm,norm_sub_rev]
  simp only [TripleGeometry.faceDelta,hv,hw,huv,Deltaf]

private lemma HardSphereB5.Lean.Geometry.PathCore.s3_cross_cyclic (v w z : Pt) : inner ℝ v (cross w z)=inner ℝ (cross v w) z := by
  simp only [TripleGeometry.inner_coords, TripleGeometry.cross_coords]
  simp
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.s3_affineIndependent_of_det (c : Fin 4 → Pt)
    (hd : det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)≠0) : AffineIndependent ℝ c := by
  classical
  apply (affineIndependent_iff_of_fintype ℝ c).mpr
  intro a ha hv i
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero Finset.univ a c ha (c 0),
    Finset.weightedVSubOfPoint_apply] at hv
  simp only [vsub_eq_sub,Fin.sum_univ_succ,Fin.sum_univ_zero] at hv ha
  simp only [Fin.succ_zero_eq_one,sub_self,smul_zero,zero_add] at hv
  let v := c 1-c 0
  let w := c 2-c 0
  let z := c 3-c 0
  change a 1 • v+(a 2 • w+(a 3 • z+0))=0 at hv
  simp only [add_zero] at hv
  have hvn := congrArg (fun u : Pt => inner ℝ u (cross w z)) hv
  have hwn := congrArg (fun u : Pt => inner ℝ u (cross z v)) hv
  have hzn := congrArg (fun u : Pt => inner ℝ u (cross v w)) hv
  have hwv : inner ℝ w (cross z v)=det3 v w z := by
    rw [s3_cross_cyclic,real_inner_comm];exact s3_cross_cyclic v w z
  have hzv : inner ℝ z (cross v w)=det3 v w z := by rw [real_inner_comm];rfl
  have hvw : inner ℝ v (cross w z)=det3 v w z := s3_cross_cyclic v w z
  have h1 : a 1*det3 v w z=0 := by
    simpa only [inner_add_left,real_inner_smul_left,inner_zero_left,
      TripleGeometry.cross_v,TripleGeometry.cross_w,hvw,mul_zero,add_zero] using hvn
  have h2 : a 2*det3 v w z=0 := by
    simpa only [inner_add_left,real_inner_smul_left,inner_zero_left,
      TripleGeometry.cross_v,TripleGeometry.cross_w,hwv,mul_zero,add_zero,zero_add] using hwn
  have h3 : a 3*det3 v w z=0 := by
    simpa only [inner_add_left,real_inner_smul_left,inner_zero_left,
      TripleGeometry.cross_v,TripleGeometry.cross_w,hzv,mul_zero,add_zero,zero_add] using hzn
  have h1z : a 1=0 := (mul_eq_zero.mp h1).resolve_right hd
  have h2z : a 2=0 := (mul_eq_zero.mp h2).resolve_right hd
  have h3z : a 3=0 := (mul_eq_zero.mp h3).resolve_right hd
  change a 0+(a 1+(a 2+(a 3+0)))=0 at ha
  have h0z : a 0=0 := by simpa only [h1z,h2z,h3z,add_zero] using ha
  fin_cases i
  · exact h0z
  · exact h1z
  · exact h2z
  · exact h3z

private theorem HardSphereB5.Lean.Geometry.PathCore.tetrahedron_metric_s5proof (hc : IsPathConfig c X Y s) :
  0 < s ∧ s < 3 ∧ AffineIndependent ℝ c ∧
  (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < Deltaf c i j k) ∧
  (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)) ^ 2 = Hpoly X Y s / 4 := by

  have hs := path_s_pos c X Y s hc
  have hs3 : s<3 := by
    by_contra hn
    have hge : 3 ≤ s := le_of_not_gt hn
    have hXY : X*Y<1 := by
      calc X*Y < X*1 := mul_lt_mul_of_pos_left hc.Y_lt_one hc.X_pos
           _ < 1 := by simpa using hc.X_lt_one
    have ht : 0 ≤ s-3 := by linarith
    have hneg : 0<(1-X)*(4-X*Y) := mul_pos (by linarith [hc.X_lt_one]) (by linarith)
    have hneg2 : 0≤X*(1-Y)*(4-Y) := mul_nonneg (mul_nonneg hc.X_pos.le (by linarith [hc.Y_lt_one])) (by linarith [hc.Y_lt_one])
    have hproduct : (X*Y-4)*(s-3)≤0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht
    have he : Hpoly X Y s= -(1-X)*(4-X*Y)-X*(1-Y)*(4-Y)-(s-3)^2+(X*Y-4)*(s-3) := by unfold Hpoly;ring
    have hH := hc.H_pos
    rw [he] at hH
    nlinarith [hH,sq_nonneg (s-3)]
  have hdet : (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0))^2=Hpoly X Y s/4 := by
    have hg := gram_from_q c 0 1 2 3
    have hp := (face_polys c X Y s hc 3).2.2.2
    change gramPoly (q c 0 1) (q c 0 2) (q c 1 2) (q c 0 3) (q c 1 3) (q c 2 3)=Hpoly X Y s at hp
    change 4*(det3 (c 1-c 0) (c 2-c 0) (c 3-c 0))^2=_ at hg
    rw [hp] at hg
    linarith
  have hdet0 : det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)≠0 := by intro hz;rw [hz] at hdet;nlinarith [hc.H_pos]
  exact ⟨hs,hs3,s3_affineIndependent_of_det c hdet0,
    fun i j k hij hik hjk => s3_face_delta_pos hc i j k hij hik hjk,hdet⟩

private theorem HardSphereB5.Lean.Geometry.PathCore.face_circumcenter_identities (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
  inner ℝ (c j-c i) (faceCircRel c i j k) = q c i j / 2 ∧
  inner ℝ (c k-c i) (faceCircRel c i j k) = q c i k / 2 ∧
  ‖faceCircRel c i j k‖ ^ 2 = q c i j * q c i k * q c j k / Deltaf c i j k ∧
  (∀ ε : ℝ, (ε=1 ∨ ε= -1) → ∀ m ∈ ({i,j,k} : Finset (Fin 4)), dist (triplePoint c i j k ε) (c m)=1) := by

  have hD := s3_face_delta_pos hc i j k hij hik hjk
  have hD0 := ne_of_gt hD
  have hQ := s3_face_Q_pos hc i j k hij hik hjk
  let v := c j-c i
  let w := c k-c i
  have hDT : TripleGeometry.faceDelta v w=Deltaf c i j k := s3_TG_delta i j k
  have hT := s3_TG_center (c:=c) i j k
  have hv : TripleGeometry.sq v=q c i j := by rw [TripleGeometry.sq_eq_norm_sq];simp only [v,q,dist_eq_norm,norm_sub_rev]
  have hw : TripleGeometry.sq w=q c i k := by rw [TripleGeometry.sq_eq_norm_sq];simp only [w,q,dist_eq_norm,norm_sub_rev]
  have hvw : TripleGeometry.sq (v-w)=q c j k := by
    rw [TripleGeometry.sq_eq_norm_sq]
    have he : v-w=c j-c k := by dsimp [v,w]; abel
    rw [he];simp only [q,dist_eq_norm]
  have hTD : TripleGeometry.faceDelta v w≠0 := by rw [hDT];exact hD0
  have h1 : inner ℝ v (faceCircRel c i j k)=q c i j/2 := by
    rw [hT,real_inner_comm,TripleGeometry.center_inner_v v w hTD,hv]
  have h2 : inner ℝ w (faceCircRel c i j k)=q c i k/2 := by
    rw [hT,real_inner_comm,TripleGeometry.center_inner_w v w hTD,hw]
  have h3 : ‖faceCircRel c i j k‖^2=q c i j*q c i k*q c j k/Deltaf c i j k := by
    rw [hT,←TripleGeometry.sq_eq_norm_sq,TripleGeometry.center_sq v w hTD,hv,hw,hvw,hDT]
  refine ⟨h1,h2,h3,?_⟩
  intro ε hε m hm
  have hε2 : ε^2=1 := by rcases hε with rfl|rfl <;> norm_num
  let o := faceCircRel c i j k
  let n := cross v w
  let a : ℝ := ε*2*√(Qf c i j k)/Deltaf c i j k
  have hN : TripleGeometry.sq n=Deltaf c i j k/4 := by
    dsimp [n]
    rw [TripleGeometry.cross_sq]
    rw [←hDT,TripleGeometry.delta_gram]
    ring
  have hoN : inner ℝ o n=0 := by
    simp only [o,faceCircRel,inner_add_left,real_inner_smul_left,n]
    change _*inner ℝ v (cross v w)+_*inner ℝ w (cross v w)=0
    rw [TripleGeometry.cross_v,TripleGeometry.cross_w];ring
  have ha2 : a^2=4*Qf c i j k/(Deltaf c i j k)^2 := by
    dsimp [a]
    have hsqrt : (√(Qf c i j k))^2=Qf c i j k := Real.sq_sqrt hQ.le
    field_simp [hD0]
    nlinarith only [hε2,hsqrt]
  have hsq : TripleGeometry.sq (o+a • n)=1 := by
    have ho : TripleGeometry.sq o=q c i j*q c i k*q c j k/Deltaf c i j k := by
      rw [TripleGeometry.sq_eq_norm_sq];exact h3
    have hNo : inner ℝ n o=0 := by rw [real_inner_comm];exact hoN
    simp only [TripleGeometry.sq,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,hoN,hNo,mul_zero,zero_add,add_zero]
    change TripleGeometry.sq o+a*(a*TripleGeometry.sq n)=1
    rw [ho,hN]
    have ha2' : a*(a*(Deltaf c i j k/4))=Qf c i j k/Deltaf c i j k := by
      calc
        _ = a^2*Deltaf c i j k/4 := by ring
        _ = Qf c i j k/Deltaf c i j k := by rw [ha2];field_simp [hD0] <;> ring
    rw [ha2']
    change q c i j*q c i k*q c j k/Deltaf c i j k +
      (Deltaf c i j k-q c i j*q c i k*q c j k)/Deltaf c i j k=1
    field_simp [hD0] <;> ring
  have hxv : inner ℝ (o+a • n) v=TripleGeometry.sq v/2 := by
    have hn : inner ℝ n v=0 := by rw [real_inner_comm];exact TripleGeometry.cross_v v w
    have ho : inner ℝ o v=q c i j/2 := by rw [real_inner_comm];exact h1
    rw [inner_add_left,real_inner_smul_left,hn,mul_zero,add_zero,ho,hv]
  have hxw : inner ℝ (o+a • n) w=TripleGeometry.sq w/2 := by
    have hn : inner ℝ n w=0 := by rw [real_inner_comm];exact TripleGeometry.cross_w v w
    have ho : inner ℝ o w=q c i k/2 := by rw [real_inner_comm];exact h2
    rw [inner_add_left,real_inner_smul_left,hn,mul_zero,add_zero,ho,hw]
  have ht : o+a • n ∈ TripleGeometry.triple v w := (TripleGeometry.mem_triple_iff v w _).mpr ⟨hsq,hxv,hxw⟩
  change ‖o+a • n‖=1 ∧ ‖o+a • n-v‖=1 ∧ ‖o+a • n-w‖=1 at ht
  have hz : triplePoint c i j k ε=c i+(o+a • n) := by dsimp [triplePoint,o,a,n,v,w];abel
  rw [hz,dist_eq_norm]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hm|hm|hm
  · rw [hm]
    have he : c i+(o+a • n)-c i=o+a • n := by abel
    rw [he];exact ht.1
  · rw [hm]
    have he : c i+(o+a • n)-c j=o+a • n-v := by dsimp [v];abel
    rw [he];exact ht.2.1
  · rw [hm]
    have he : c i+(o+a • n)-c k=o+a • n-w := by dsimp [w];abel
    rw [he];exact ht.2.2

open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric : ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s),
  0 < s ∧ s < 3 ∧ AffineIndependent ℝ c ∧
  (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < Deltaf c i j k) ∧
  (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)) ^ 2 = Hpoly X Y s / 4 := by
  exact @HardSphereB5.Lean.Geometry.PathCore.tetrahedron_metric_s5proof
