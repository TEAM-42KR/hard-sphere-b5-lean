import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_CircleArc_intervalIntersection
import HardSphereB5Lean.Theorems.Thm_CircleArc_arcIntersectionCases
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_pair_normal_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_pair_normalized_frame
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

private lemma HardSphereB5.Lean.Geometry.PathCore.two_point_retained_count (p m z : Pt) (a b : ℝ) (hpm : p ≠ m) (hb : 0 < b)
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

private lemma HardSphereB5.Lean.Geometry.PathCore.margin_selector (H D Q P A a b : ℝ) (hH : 0 < H) (hD : 0 < D)
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

open HardSphereB5.Lean.Geometry.PathCore
set_option maxHeartbeats 1000000

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_near_threshold (X Y t : ℝ)
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

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_near_support_bound (X Y t : ℝ)
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

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_near_A1_neg (X Y t : ℝ)
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

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_signs_near_gt (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hs1 : s < 1) (hYX : Y < X) :
    0 < Apoly X Y s 0 ∧ Apoly X Y s 1 < 0 ∧
    0 < Apoly X Y s 2 ∧ Apoly X Y s 3 < 0 := by
  let t := 1-s
  have ht : 0 < t := by dsimp [t]; linarith
  have hs : s = 1-t := by dsimp [t]; ring
  rw [hs] at hH hP ⊢
  have hT := sliver_near_threshold X Y t hX0 hX1 hY0 hY1 ht hYX hP
  have hU := sliver_near_support_bound X Y t hX0 hY0 hY1 ht hYX hH
  have hA1 := sliver_near_A1_neg X Y t hX0 hX1 hY0 hY1 ht hYX hP
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

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_signs_near_lt (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hs1 : s < 1) (hXY : X < Y) :
    Apoly X Y s 0 < 0 ∧ 0 < Apoly X Y s 1 ∧
    Apoly X Y s 2 < 0 ∧ 0 < Apoly X Y s 3 := by
  have hHs : Hpoly Y X s = Hpoly X Y s := by unfold Hpoly; ring
  have hPs : P4poly Y X s = P4poly X Y s := by unfold P4poly; ring
  have hh : 0 < Hpoly Y X s := by rwa [hHs]
  have hp : P4poly Y X s < 0 := by rwa [hPs]
  rcases sliver_signs_near_gt Y X s hY0 hY1 hX0 hX1 hh hs0 hp hs1 hXY with
    ⟨ha0, ha1, ha2, ha3⟩
  have he0 : Apoly X Y s 0 = Apoly Y X s 1 := by simp [Apoly] <;> ring <;> simp
  have he1 : Apoly X Y s 1 = Apoly Y X s 0 := by simp [Apoly] <;> ring <;> simp
  have he2 : Apoly X Y s 2 = Apoly Y X s 3 := by simp [Apoly] <;> ring <;> simp
  have he3 : Apoly X Y s 3 = Apoly Y X s 2 := by simp [Apoly] <;> ring <;> simp
  exact ⟨by rwa [he0], by rwa [he1], by rwa [he2], by rwa [he3]⟩

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_signs_far (X Y s : ℝ)
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

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_s_ne_one (X Y s : ℝ)
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

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_near_ne_diagonal (X Y s : ℝ)
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

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_regions (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0) :
    (s < 1 ∧ Y < X) ∨ (s < 1 ∧ X < Y) ∨ 1 < s := by
  have hsne := sliver_s_ne_one X Y s hX0 hX1 hY0 hY1 hP
  rcases lt_or_gt_of_ne hsne with hs | hs
  · have hxyne := sliver_near_ne_diagonal X Y s hX0 hX1 hY0 hY1 hH hP hs
    rcases lt_or_gt_of_ne hxyne with hxy | hyx
    · exact Or.inr (Or.inl ⟨hs,hxy⟩)
    · exact Or.inl ⟨hs,hyx⟩
  · exact Or.inr (Or.inr hs)

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_exactly_one (X Y s : ℝ)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0) :
    ∃! k : Fin 3, ![s < 1 ∧ Y < X, s < 1 ∧ X < Y, 1 < s] k := by
  rcases sliver_regions X Y s hX0 hX1 hY0 hY1 hH hs0 hP with h | h | h
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

open HardSphereB5.Lean.Geometry.PathCore

private def HardSphereB5.Lean.Geometry.PathCore.SliverCountTable (c : Fin 4 → Pt) (X Y s : ℝ) : Prop :=
  ((s < 1 ∧ Y < X) → nRet c = ![0, 2, 0, 2]) ∧
  ((s < 1 ∧ X < Y) → nRet c = ![2, 0, 2, 0]) ∧
  (1 < s → nRet c = ![2, 2, 0, 0])

private def HardSphereB5.Lean.Geometry.PathCore.SliverCommonTable (c : Fin 4 → Pt) (X Y s : ℝ) : Prop :=
  ((s < 1 ∧ Y < X) → ∀ i j : Fin 4, i ≠ j →
    (isCommon c i j ↔ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0))) ∧
  ((s < 1 ∧ X < Y) → ∀ i j : Fin 4, i ≠ j →
    (isCommon c i j ↔ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) ∧
  (1 < s → ∀ i j : Fin 4, i ≠ j →
    (isCommon c i j ↔ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)))

private theorem HardSphereB5.Lean.Geometry.PathCore.common02_of_count_table (c : Fin 4 → Pt)
    (ht : nRet c = ![0, 2, 0, 2]) :
    ∀ i j : Fin 4, i ≠ j →
      (isCommon c i j ↔ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) := by
  intro i j hij
  unfold isCommon
  rw [ht]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem HardSphereB5.Lean.Geometry.PathCore.common13_of_count_table (c : Fin 4 → Pt)
    (ht : nRet c = ![2, 0, 2, 0]) :
    ∀ i j : Fin 4, i ≠ j →
      (isCommon c i j ↔ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) := by
  intro i j hij
  unfold isCommon
  rw [ht]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem HardSphereB5.Lean.Geometry.PathCore.common23_of_count_table (c : Fin 4 → Pt)
    (ht : nRet c = ![2, 2, 0, 0]) :
    ∀ i j : Fin 4, i ≠ j →
      (isCommon c i j ↔ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
  intro i j hij
  unfold isCommon
  rw [ht]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_table_of_selector (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0) :
    SliverCountTable c X Y s ∧ SliverCommonTable c X Y s := by
  have ht0 (hr : s < 1 ∧ Y < X) : nRet c = ![0, 2, 0, 2] := by
    rcases sliver_signs_near_gt X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
      hc.H_pos hs0 hP hr.1 hr.2 with ⟨ha0,ha1,ha2,ha3⟩
    have hn0 : ¬ Apoly X Y s 0 < 0 := not_lt.mpr ha0.le
    have hn2 : ¬ Apoly X Y s 2 < 0 := not_lt.mpr ha2.le
    funext l
    fin_cases l <;> simp [hSel, hn0,ha1,hn2,ha3]
  have ht1 (hr : s < 1 ∧ X < Y) : nRet c = ![2, 0, 2, 0] := by
    rcases sliver_signs_near_lt X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
      hc.H_pos hs0 hP hr.1 hr.2 with ⟨ha0,ha1,ha2,ha3⟩
    have hn1 : ¬ Apoly X Y s 1 < 0 := not_lt.mpr ha1.le
    have hn3 : ¬ Apoly X Y s 3 < 0 := not_lt.mpr ha3.le
    funext l
    fin_cases l <;> simp [hSel, ha0,hn1,ha2,hn3]
  have ht2 (hr : 1 < s) : nRet c = ![2, 2, 0, 0] := by
    rcases sliver_signs_far X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
      hc.H_pos hs0 hP hr with ⟨ha0,ha1,ha2,ha3⟩
    have hn2 : ¬ Apoly X Y s 2 < 0 := not_lt.mpr ha2.le
    have hn3 : ¬ Apoly X Y s 3 < 0 := not_lt.mpr ha3.le
    funext l
    fin_cases l <;> simp [hSel, ha0,ha1,hn2,hn3]
  refine ⟨⟨ht0,ht1,ht2⟩, ?_⟩
  exact ⟨fun hr => common02_of_count_table c (ht0 hr),
    fun hr => common13_of_count_table c (ht1 hr),
    fun hr => common23_of_count_table c (ht2 hr)⟩

private def HardSphereB5.Lean.Geometry.PathCore.SliverIncidenceLedger (c : Fin 4 → Pt) : Prop :=
  (∑ l : Fin 4, nRet c l) = 4 ∧
  ∃ i j : Fin 4, i ≠ j ∧ isCommon c i j ∧
    (∀ a b : Fin 4, a ≠ b →
      (isCommon c a b ↔ (a = i ∧ b = j) ∨ (a = j ∧ b = i))) ∧
    (∀ a : Fin 4, (∑ l ∈ (Finset.univ : Finset (Fin 4)).erase a, nRet c l) =
      if a = i ∨ a = j then 4 else 2)

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_incidence_of_count_table (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hTable : SliverCountTable c X Y s) : SliverIncidenceLedger c := by
  rcases hTable with ⟨ht0,ht1,ht2⟩
  rcases sliver_regions X Y s hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
    hc.H_pos hs0 hP with hr | hr | hr
  · have ht := ht0 hr
    have hcom := common02_of_count_table c ht
    refine ⟨?_,0,2,by decide,?_,hcom,?_⟩
    · rw [ht]
      decide
    · exact (hcom 0 2 (by decide)).mpr (by simp)
    · intro a
      rw [ht]
      fin_cases a <;> decide
  · have ht := ht1 hr
    have hcom := common13_of_count_table c ht
    refine ⟨?_,1,3,by decide,?_,hcom,?_⟩
    · rw [ht]
      decide
    · exact (hcom 1 3 (by decide)).mpr (by simp)
    · intro a
      rw [ht]
      fin_cases a <;> decide
  · have ht := ht2 hr
    have hcom := common23_of_count_table c ht
    refine ⟨?_,2,3,by decide,?_,hcom,?_⟩
    · rw [ht]
      decide
    · exact (hcom 2 3 (by decide)).mpr (by simp)
    · intro a
      rw [ht]
      fin_cases a <;> decide

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_incidence_of_selector (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hP : P4poly X Y s < 0)
    (hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0) :
    SliverIncidenceLedger c :=
  sliver_incidence_of_count_table c X Y s hc hs0 hP
    (sliver_table_of_selector c X Y s hc hs0 hP hSel).1

private theorem HardSphereB5.Lean.Geometry.PathCore.lemma64d_of_incidence (c : Fin 4 → Pt) (X Y s Bminus : ℝ)
    (hc : IsPathConfig c X Y s) (hs0 : 0 < s) (hs1 : s < 1)
    (hPne : P4poly X Y s ≠ 0)
    (hBulk : 0 < P4poly X Y s → ∀ l, nRet c l = 1)
    (hTable : P4poly X Y s < 0 → SliverCountTable c X Y s)
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

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace

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

private lemma HardSphereB5.Lean.Geometry.PathCore.q_nonneg' (c : Fin 4 → Pt) (i j : Fin 4) : 0 ≤ q c i j := by unfold q; positivity

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

private lemma HardSphereB5.Lean.Geometry.PathCore.norm_sub_base (x y p : Pt) : ‖(x-p)-(y-p)‖ = ‖x-y‖ := by
  congr 1; abel

private lemma HardSphereB5.Lean.Geometry.PathCore.triplePts_translate (c : Fin 4 → Pt) (l : Fin 4) :
    triplePts c l = {x | x - c (faceVerts l).1 ∈
      TripleGeometry.triple (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1)} := by
  ext x
  fin_cases l <;>
    simp [triplePts, faceVerts, Fin.forall_fin_succ, TripleGeometry.triple,
      dist_eq_norm, norm_sub_base] <;> tauto

private lemma HardSphereB5.Lean.Geometry.PathCore.TG_sq_q (c : Fin 4 → Pt) (i j : Fin 4) : TripleGeometry.sq (c j-c i) = q c i j := by
  exact (q_inner c i j).symm

private lemma HardSphereB5.Lean.Geometry.PathCore.TG_sq_diff_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    TripleGeometry.sq ((c j-c i)-(c k-c i)) = q c j k := by
  have he : (c j-c i)-(c k-c i) = c j-c k := by abel
  rw [he, TG_sq_q, q_symm']

private lemma HardSphereB5.Lean.Geometry.PathCore.face_TG_D (c : Fin 4 → Pt) (l : Fin 4) :
    TripleGeometry.faceDelta (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) =
    Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 := by
  simp only [TripleGeometry.faceDelta, TG_sq_q, TG_sq_diff_q, Deltaf]

private lemma HardSphereB5.Lean.Geometry.PathCore.face_TG_Q (c : Fin 4 → Pt) (l : Fin 4) :
    TripleGeometry.faceQ (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) = Qface c l := by
  simp only [TripleGeometry.faceQ, TG_sq_q, TG_sq_diff_q, Qface, Qf]

private lemma HardSphereB5.Lean.Geometry.PathCore.normal_projection_identity (v w z : Pt) (hD : 0 < TripleGeometry.faceDelta v w) :
    TripleGeometry.faceDelta v w * (inner ℝ z (TripleGeometry.orientedNormal v w z))^2 =
      4 * (inner ℝ z (cross v w))^2 := by
  have hn := ne_of_gt (TripleGeometry.cross_norm_pos v w hD)
  have hd : TripleGeometry.faceDelta v w = 4*‖cross v w‖^2 := by
    rw [TripleGeometry.delta_gram, ← TripleGeometry.cross_sq, TripleGeometry.sq_eq_norm_sq]
  rw [hd]
  unfold TripleGeometry.orientedNormal
  split_ifs <;> simp only [inner_neg_right, real_inner_smul_right]
  all_goals field_simp [hn]
  all_goals ring

private lemma HardSphereB5.Lean.Geometry.PathCore.numerator_identity (v w z : Pt) (hD : TripleGeometry.faceDelta v w ≠ 0) :
    TripleGeometry.faceDelta v w * (TripleGeometry.sq z - 2*inner ℝ z (TripleGeometry.center v w)) =
      faceAPoly (TripleGeometry.sq v) (TripleGeometry.sq w) (TripleGeometry.sq (v-w))
        (TripleGeometry.sq z) (TripleGeometry.sq (z-v)) (TripleGeometry.sq (z-w)) := by
  simp only [TripleGeometry.center, inner_add_right, real_inner_smul_right, faceAPoly]
  have hd : DeltaT (TripleGeometry.sq v) (TripleGeometry.sq w)
      (TripleGeometry.sq (v-w)) = TripleGeometry.faceDelta v w := rfl
  rw [hd]
  simp only [TripleGeometry.sq_sub]
  field_simp [hD]
  rw [TripleGeometry.delta_gram]
  ring

private theorem HardSphereB5.Lean.Geometry.PathCore.nRet_coordinate_selector (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (l : Fin 4) :
    nRet c l = if 0 < P4poly X Y s then 1 else if Apoly X Y s l < 0 then 2 else 0 := by
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  let v := c j-c i
  let w := c k-c i
  let z := c l-c i
  let D := TripleGeometry.faceDelta v w
  let Q := TripleGeometry.faceQ v w
  let N := TripleGeometry.orientedNormal v w z
  let h := TripleGeometry.height v w
  let o := TripleGeometry.center v w
  let p := c i + (o+h•N)
  let m := c i + (o-h•N)
  let a := TripleGeometry.sq z - 2*inner ℝ z o
  let b := 2*h*inner ℝ z N
  have hDP : D = Dpoly X Y s l := (face_TG_D c l).trans (face_polys c X Y s hc l).2.1
  have hQP : Q = Qpoly X Y s l := (face_TG_Q c l).trans (face_polys c X Y s hc l).1
  have hD : 0 < D := by rw [hDP]; exact path_Dpoly_pos c X Y s hc l
  have hQ : 0 < Q := by rw [hQP]; exact path_Qpoly_pos c X Y s hc l
  have hQface : 0 < Qface c l := by rw [← face_TG_Q c l]; exact hQ
  have hdet : 4*(inner ℝ z (cross v w))^2 = Hpoly X Y s := by
    have hg := gram_from_q c i j k l
    rw [(face_polys c X Y s hc l).2.2.2] at hg
    simpa only [real_inner_comm] using hg
  have hG : inner ℝ z (cross v w) ≠ 0 := by intro hz; rw [hz] at hdet; nlinarith [hc.H_pos]
  have hn : 0 < inner ℝ z N := TripleGeometry.normal_oriented v w z hD hG
  have hh : 0 < h := TripleGeometry.height_pos v w hD hQ
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hh) hn
  have hpm : p ≠ m := by
    exact fun he => TripleGeometry.triple_points_ne v w z hD hQ (add_left_cancel he)
  have htr : triplePts c l = {p,m} := by
    rw [triplePts_translate c l]
    change {x | x-c i ∈ TripleGeometry.triple v w} = {p,m}
    rw [TripleGeometry.triple_exact v w z hD hQ]
    ext x
    simp [p,m,o,h,N,Set.mem_insert_iff,Set.mem_singleton_iff,sub_eq_iff_eq_add,add_comm]
  have hp : (dist p (c l))^2-1 = a-b := by
    have he : p-c l = o+h•N-z := by dsimp [p,z]; abel
    rw [dist_eq_norm,he]
    exact TripleGeometry.fourth_sq_formula v w z h hD hQ rfl
  have hm : (dist m (c l))^2-1 = a+b := by
    have he : m-c l = o+(-h)•N-z := by dsimp [m,z]; simp only [neg_smul]; abel
    rw [dist_eq_norm,he,TripleGeometry.fourth_sq_formula v w z (-h) hD hQ (neg_sq h)]
    dsimp [a,b]; ring
  have ha : D*a = Apoly X Y s l := by
    have hx := numerator_identity v w z (ne_of_gt hD)
    change D*a = _ at hx
    dsimp [v,w,z] at hx
    simp only [TG_sq_q, TG_sq_diff_q] at hx
    rw [q_symm' c l j, q_symm' c l k] at hx
    exact hx.trans (face_polys c X Y s hc l).2.2.1
  have hhd : D*h^2 = Q := by
    change D * (Real.sqrt (Q/D))^2 = Q
    rw [Real.sq_sqrt (div_nonneg (le_of_lt hQ) (le_of_lt hD))]
    field_simp [ne_of_gt hD]
    <;> ring
  have hnd : D*(inner ℝ z N)^2 = Hpoly X Y s :=
    (normal_projection_identity v w z hD).trans hdet
  have hb2 : D^2*b^2 = 4*Hpoly X Y s*Qpoly X Y s l := by
    calc D^2*b^2 = 4*(D*h^2)*(D*(inner ℝ z N)^2) := by dsimp [b]; ring
         _ = 4*Q*Hpoly X Y s := by rw [hhd,hnd]
         _ = 4*Hpoly X Y s*Qpoly X Y s l := by rw [hQP]; ring
  have hdisc : Apoly X Y s l^2 - 4*Hpoly X Y s*Qpoly X Y s l = -D*P4poly X Y s := by
    rw [hDP]; exact cayley_menger_face_identity X Y s l
  have hs := margin_selector (Hpoly X Y s) D (Qpoly X Y s l) (P4poly X Y s)
    (Apoly X Y s l) a b hc.H_pos hD (path_Qpoly_pos c X Y s hc l) hb ha hb2 hdisc
  have hset : triplePts c l ∩ Kset c = {p,m} ∩ Metric.closedBall (c l) 1 := by
    rw [retained_set_eq,htr]
    ext x; simp [Metric.mem_closedBall,dist_comm]
  rw [nRet,if_pos hQface,hset]
  rw [two_point_retained_count p m (c l) a b hpm hb hp hm]
  by_cases hbulk : 0 < P4poly X Y s
  · rw [if_pos hbulk, if_pos (hs.1 hbulk)]
  · have hsliv : P4poly X Y s < 0 := lt_of_le_of_ne (le_of_not_gt hbulk) hP
    have hba := hs.2.1 hsliv
    rw [if_neg hbulk,if_neg (not_lt_of_ge (le_of_lt hba))]
    by_cases hA : Apoly X Y s l < 0
    · rw [if_pos hA,if_pos ⟨hba,hs.2.2.mpr hA⟩]
    · rw [if_neg hA,if_neg (fun hh => hA (hs.2.2.mp hh.2)),if_pos hba]

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private theorem HardSphereB5.Lean.Geometry.PathCore.bulk_incidence {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) :
    (∀ l, nRet c l = 1) ∧ ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 := by
  have hn : ∀ l, nRet c l = 1 := by
    intro l
    rw [nRet_coordinate_selector c X Y s hc (ne_of_gt hP) l,if_pos hP]
  exact ⟨hn,bulk_patch_counts c hn⟩

private lemma HardSphereB5.Lean.Geometry.PathCore.sliver_selector {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) :
    ∀ l, nRet c l = if 0 < Qpoly X Y s l ∧ Apoly X Y s l < 0 then 2 else 0 := by
  intro l
  rw [nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l,
    if_neg (not_lt_of_ge (le_of_lt hP))]
  simp only [path_Qpoly_pos c X Y s hc l, true_and]

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_incidence {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) :
    (∀ l, nRet c l = if 0 < Qpoly X Y s l ∧ Apoly X Y s l < 0 then 2 else 0) ∧
      ∑ l, nRet c l = 4 ∧
      ∃ i j, i ≠ j ∧ isCommon c i j ∧
        ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = if m = i ∨ m = j then 4 else 2 := by
  have hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0 := by
    intro l
    rw [nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l,
      if_neg (not_lt_of_ge (le_of_lt hP))]
  have hledger := sliver_incidence_of_selector c X Y s hc (path_s_pos c X Y s hc) hP hSel
  obtain ⟨hsum,i,j,hij,hcommon,hunique,hcounts⟩ := hledger
  exact ⟨sliver_selector hc hP,hsum,i,j,hij,hcommon,hcounts⟩

private theorem HardSphereB5.Lean.Geometry.PathCore.sliver_table {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) :
    (s < 1 → Y < X → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (2, 0, 2, 0) ∧ isCommon c 0 2) ∧
    (s < 1 → X < Y → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 2, 0, 2) ∧ isCommon c 1 3) ∧
    (1 < s → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 0, 2, 2) ∧ isCommon c 2 3) := by
  have hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0 := by
    intro l
    rw [nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l,
      if_neg (not_lt_of_ge (le_of_lt hP))]
  obtain ⟨hTable,hCommon⟩ := sliver_table_of_selector c X Y s hc (path_s_pos c X Y s hc) hP hSel
  refine ⟨?_,?_,?_⟩
  · intro hs hyx
    have ht := hTable.1 ⟨hs,hyx⟩
    refine ⟨?_,(hCommon.1 ⟨hs,hyx⟩ 0 2 (by decide)).mpr (by simp)⟩
    simp [ht]
  · intro hs hxy
    have ht := hTable.2.1 ⟨hs,hxy⟩
    refine ⟨?_,(hCommon.2.1 ⟨hs,hxy⟩ 1 3 (by decide)).mpr (by simp)⟩
    simp [ht]
  · intro hs
    have ht := hTable.2.2 hs
    refine ⟨?_,(hCommon.2.2 hs 2 3 (by decide)).mpr (by simp)⟩
    simp [ht]

private theorem HardSphereB5.Lean.Geometry.PathCore.lemma64d {c : Fin 4 → Pt} {X Y s : ℝ} (Bminus : ℝ)
    (hc : IsPathConfig c X Y s) (hs1 : s < 1) (hPne : P4poly X Y s ≠ 0)
    (hBulkIff : 0 < P4poly X Y s ↔ Bminus < X)
    (hNearGt : P4poly X Y s < 0 → (Y < X ↔ s < (1-Y)^2))
    (hNearLt : P4poly X Y s < 0 → (X < Y ↔ (1-Y)^2 < s)) :
    (Bminus < X → nRet c 1 = 1 ∧ nRet c 0 = 1) ∧
    (X < Bminus ∧ s < (1-Y)^2 → nRet c 1 = 2 ∧ nRet c 0 = 0) ∧
    (X < Bminus ∧ (1-Y)^2 < s → nRet c 1 = 0 ∧ nRet c 0 = 2) := by
  apply lemma64d_of_incidence c X Y s Bminus hc (path_s_pos c X Y s hc) hs1 hPne
  · intro hP; exact (bulk_incidence hc hP).1
  · intro hP
    have hSel : ∀ l, nRet c l = if Apoly X Y s l < 0 then 2 else 0 := by
      intro l
      rw [nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l,
        if_neg (not_lt_of_ge (le_of_lt hP))]
    exact (sliver_table_of_selector c X Y s hc (path_s_pos c X Y s hc) hP hSel).1
  · exact hBulkIff
  · exact hNearGt
  · exact hNearLt

noncomputable section
open SphereGeom
open scoped RealInnerProductSpace

private theorem CircleArc.pair_circle_on_spheres (a b : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (hperp : ∀ i, inner ℝ (b - a) (e i) = 0)
    (hd : dist a b < 2) (t : ℝ) :
    circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1)
      (Real.sqrt (1 - dist a b ^ 2 / 4)) t ∈ Metric.sphere a 1 ∩ Metric.sphere b 1 := by
  let r : ℝ := Real.sqrt (1 - dist a b ^ 2 / 4)
  let u : E3 := Real.cos t • e 0 + Real.sin t • e 1
  have he00 : inner ℝ (e 0) (e 0) = 1 := by
    rw [real_inner_self_eq_norm_sq, he.1 0]; norm_num
  have he11 : inner ℝ (e 1) (e 1) = 1 := by
    rw [real_inner_self_eq_norm_sq, he.1 1]; norm_num
  have he01 : inner ℝ (e 0) (e 1) = 0 := he.inner_eq_zero (by decide)
  have he10 : inner ℝ (e 1) (e 0) = 0 := he.inner_eq_zero (by decide)
  have hu : inner ℝ u u = 1 := by
    dsimp [u]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, he00, he11, he01, he10]
    nlinarith [Real.cos_sq_add_sin_sq t]
  have hvu : inner ℝ (b - a) u = 0 := by
    simp [u, inner_add_right, real_inner_smul_right, hperp]
  have huv : inner ℝ u (b - a) = 0 := by
    rw [real_inner_comm]; exact hvu
  have hv : inner ℝ (b - a) (b - a) = dist a b ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm]
  have hr : r ^ 2 = 1 - dist a b ^ 2 / 4 := by
    apply Real.sq_sqrt
    nlinarith [dist_nonneg (x := a) (y := b)]
  have hxa : circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a =
      (1 / 2 : ℝ) • (b - a) + r • u := by
    dsimp [circlePt, u]; module
  have hxb : circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b =
      (-1 / 2 : ℝ) • (b - a) + r • u := by
    dsimp [circlePt, u]; module
  have hna : ‖circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hxa]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvu, huv, hv, hu]
    nlinarith [hr]
  have hnb : ‖circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hxb]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvu, huv, hv, hu]
    nlinarith [hr]
  constructor <;> rw [Metric.mem_sphere, dist_eq_norm]
  · nlinarith [norm_nonneg (circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a)]
  · nlinarith [norm_nonneg (circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b)]

open CircleArc
private theorem CircleArc.ball_iff_inner (a k x : E3) (hx : x ∈ Metric.sphere a 1) :
    x ∈ Metric.closedBall k 1 ↔
      dist a k ^ 2 / 2 ≤ inner ℝ (x - a) (k - a) := by
  have hxa : ‖x - a‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  have hw : ‖k - a‖ = dist a k := by rw [← dist_eq_norm, dist_comm]
  have hvec : x - k = (x - a) - (k - a) := by abel
  have hsq : dist x k ^ 2 = 1 - 2 * inner ℝ (x - a) (k - a) + dist a k ^ 2 := by
    rw [dist_eq_norm, hvec, norm_sub_sq_real, hxa, hw]; norm_num
  rw [Metric.mem_closedBall]
  constructor
  · intro h
    nlinarith [dist_nonneg (x := x) (y := k)]
  · intro h
    nlinarith [dist_nonneg (x := x) (y := k)]

open MeasureTheory SphereGeom

noncomputable section

private theorem InnerAngle.angle_eq_arg_of_scaled_gram
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (t x y : ℝ) (ht : 0 < t) (hy : 0 < y)
    (hi : t * inner ℝ u v = x)
    (hg : t ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) = x ^ 2 + y ^ 2) :
    InnerProductGeometry.angle u v = Complex.arg ⟨x, y⟩ := by
  have hn : ‖(⟨x, y⟩ : ℂ)‖ = t * (‖u‖ * ‖v‖) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [← Complex.normSq_eq_norm_sq]
    change x * x + y * y = (t * (‖u‖ * ‖v‖)) ^ 2
    nlinarith [hg]
  rw [InnerProductGeometry.angle, Complex.arg_of_im_pos hy, hn]
  congr 1
  rw [← hi]
  simp only [mul_div_mul_left _ _ (ne_of_gt ht)]

open HardSphereB5.Lean.Geometry.PathCore

open HardSphereB5.Lean (Pt)

private lemma HardSphereB5.Lean.Geometry.PathCore.near_q_symm (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

private lemma HardSphereB5.Lean.Geometry.PathCore.near_norm_sub_q (c : Fin 4 → Pt) (i j : Fin 4) :
    ‖c i - c j‖ ^ 2 = q c i j := by
  rw [q, dist_eq_norm]

private lemma HardSphereB5.Lean.Geometry.PathCore.near_inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    2 * inner ℝ (c j - c i) (c k - c i) =
      q c i j + q c i k - q c j k := by
  have hdiff : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [← pow_two]
  rw [hdiff, near_norm_sub_q, near_norm_sub_q, near_norm_sub_q,
    near_q_symm c j i, near_q_symm c k i]
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.near_s_pos {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s) :
    0 < s := by
  have h23 : c 2 ≠ c 3 := by
    intro heq
    have hh : 1 = Y := by
      calc
        1 = q c 0 2 := hc.q02.symm
        _ = q c 0 3 := by rw [q, q, heq]
        _ = Y := hc.q03
    linarith [hc.Y_lt_one]
  rw [← hc.q23, q]
  exact sq_pos_of_pos (dist_pos.mpr h23)

private lemma HardSphereB5.Lean.Geometry.PathCore.near_raw_inner {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s) :
    inner ℝ (c 3 - c 2) (c 3 - c 2) = s ∧
    inner ℝ (c 0 - c 2) (c 0 - c 2) = 1 ∧
    inner ℝ (c 1 - c 2) (c 1 - c 2) = X ∧
    2 * inner ℝ (c 0 - c 2) (c 1 - c 2) = X ∧
    2 * inner ℝ (c 0 - c 2) (c 3 - c 2) = 1 + s - Y ∧
    2 * inner ℝ (c 1 - c 2) (c 3 - c 2) = X + s - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [real_inner_self_eq_norm_sq, near_norm_sub_q, near_q_symm, hc.q23]
  · rw [real_inner_self_eq_norm_sq, near_norm_sub_q, hc.q02]
  · rw [real_inner_self_eq_norm_sq, near_norm_sub_q, hc.q12]
  · have hh := near_inner_from_q c 2 0 1
    rw [near_q_symm c 2 0, near_q_symm c 2 1, hc.q02, hc.q12, hc.q01] at hh
    linarith
  · have hh := near_inner_from_q c 2 0 3
    rw [near_q_symm c 2 0, hc.q02, hc.q23, hc.q03] at hh
    exact hh
  · have hh := near_inner_from_q c 2 1 3
    rw [near_q_symm c 2 1, hc.q12, hc.q23, hc.q13] at hh
    exact hh

private lemma HardSphereB5.Lean.Geometry.PathCore.near_perpProj_inner (v a b : Pt) (hv : inner ℝ v v ≠ 0) :
    inner ℝ (perpProj v a) (perpProj v b) =
      inner ℝ a b - inner ℝ a v * inner ℝ b v / inner ℝ v v := by
  unfold perpProj
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right]
  rw [real_inner_comm v b]
  field_simp [hv]
  <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.near_projection_gram {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s) :
    (4 * s) * inner ℝ
      (perpProj (c 3 - c 2) (c 0 - c 2))
      (perpProj (c 3 - c 2) (c 1 - c 2)) =
      X * Y + (s - 1) * (X + Y) + 1 - s ^ 2 ∧
    (4 * s) * ‖perpProj (c 3 - c 2) (c 0 - c 2)‖ ^ 2 =
      4 * s - (1 + s - Y) ^ 2 ∧
    (4 * s) * ‖perpProj (c 3 - c 2) (c 1 - c 2)‖ ^ 2 =
      4 * s * X - (X + s - 1) ^ 2 := by
  rcases near_raw_inner hc with ⟨hv, ha, hb, hab, hav, hbv⟩
  have hs0 : s ≠ 0 := ne_of_gt (near_s_pos hc)
  have hv0 : inner ℝ (c 3 - c 2) (c 3 - c 2) ≠ 0 := by rwa [hv]
  have hab' : inner ℝ (c 0 - c 2) (c 1 - c 2) = X / 2 := by linarith
  have hav' : inner ℝ (c 0 - c 2) (c 3 - c 2) = (1 + s - Y) / 2 := by linarith
  have hbv' : inner ℝ (c 1 - c 2) (c 3 - c 2) = (X + s - 1) / 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [near_perpProj_inner _ _ _ hv0, hv, hab', hav', hbv']
    field_simp [hs0]
    <;> ring
  · rw [← real_inner_self_eq_norm_sq, near_perpProj_inner _ _ _ hv0, hv, ha, hav']
    field_simp [hs0]
    <;> ring
  · rw [← real_inner_self_eq_norm_sq, near_perpProj_inner _ _ _ hv0, hv, hb, hbv']
    field_simp [hs0]
    <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.near_gram_polynomial (X Y s : ℝ) :
    (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ^ 2 + 4 * s * Hpoly X Y s =
      (4 * s - (1 + s - Y) ^ 2) * (4 * s * X - (X + s - 1) ^ 2) := by
  unfold Hpoly
  ring

private theorem HardSphereB5.Lean.Geometry.PathCore.near_moving_point_angle {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (_hs : s < 1) :
    phiE c 2 3 =
      atan2 (2 * √(s * Hpoly X Y s))
        (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) := by
  have hspos : 0 < s := near_s_pos hc
  have hhpos : 0 < s * Hpoly X Y s := mul_pos hspos hc.H_pos
  rcases near_projection_gram hc with ⟨hi, hna, hnb⟩
  have hg : (4 * s) ^ 2 *
      (‖perpProj (c 3 - c 2) (c 0 - c 2)‖ ^ 2 *
        ‖perpProj (c 3 - c 2) (c 1 - c 2)‖ ^ 2) =
      (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ^ 2 +
        (2 * √(s * Hpoly X Y s)) ^ 2 := by
    calc
      _ = ((4 * s) * ‖perpProj (c 3 - c 2) (c 0 - c 2)‖ ^ 2) *
          ((4 * s) * ‖perpProj (c 3 - c 2) (c 1 - c 2)‖ ^ 2) := by ring
      _ = (4 * s - (1 + s - Y) ^ 2) * (4 * s * X - (X + s - 1) ^ 2) := by rw [hna, hnb]
      _ = (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ^ 2 + 4 * s * Hpoly X Y s :=
        (near_gram_polynomial X Y s).symm
      _ = _ := by rw [mul_pow, Real.sq_sqrt hhpos.le]; ring
  have ho1 : oth1 (2 : Fin 4) 3 = 0 := by
    have h02 : (0 : Fin 4) ≠ 2 := by decide
    have h03 : (0 : Fin 4) ≠ 3 := by decide
    simp [oth1, h02, h03]
  have ho2 : oth2 (2 : Fin 4) 3 = 1 := by norm_num [oth2]
  rw [phiE, ho1, ho2, dihedral]
  exact InnerAngle.angle_eq_arg_of_scaled_gram _ _ (4 * s) _ _
    (by positivity) (by positivity) hi hg

open HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_q_symm (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_s_pos (hc : IsPathConfig c X Y s) : 0 < s := by
  have hne : c 2 ≠ c 3 := by
    intro h
    have hy : Y = 1 := by
      calc
        Y = q c 0 3 := hc.q03.symm
        _ = q c 0 2 := by simp only [q, h]
        _ = 1 := hc.q02
    linarith [hc.Y_lt_one]
  rw [← hc.q23, q]
  exact sq_pos_of_pos (dist_pos.mpr hne)

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_betaA_23_0 (hc : IsPathConfig c X Y s) :
    betaA c 2 3 0 =
      atan2 (2 * Real.sqrt (Qpoly X Y s 1))
        (Real.sqrt s * (1 + Y - s)) := by
  have h20 : q c 2 0 = 1 := (p3_q_symm 2 0).trans hc.q02
  have h30 : q c 3 0 = Y := (p3_q_symm 3 0).trans hc.q03
  have hQ : Qf c 2 3 0 = Qpoly X Y s 1 := by
    simp only [Qf, QT, DeltaT, hc.q23, h20, h30]
    norm_num [Qpoly]
    ring
  simp only [betaA, hQ, hc.q23, h20, h30]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_betaA_23_1 (hc : IsPathConfig c X Y s) :
    betaA c 2 3 1 =
      atan2 (2 * Real.sqrt (Qpoly X Y s 0))
        (Real.sqrt s * (1 + X - s)) := by
  have h21 : q c 2 1 = X := (p3_q_symm 2 1).trans hc.q12
  have h31 : q c 3 1 = 1 := (p3_q_symm 3 1).trans hc.q13
  have hQ : Qf c 2 3 1 = Qpoly X Y s 0 := by
    simp only [Qf, QT, DeltaT, hc.q23, h21, h31]
    norm_num [Qpoly]
    ring
  simp only [betaA, hQ, hc.q23, h21, h31]
  congr 2 <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_near_numerators_pos (hc : IsPathConfig c X Y s) (hs : s < 1) :
    0 < 1 + Y - s ∧ 0 < 1 + X - s := by
  constructor <;> linarith [hc.X_pos, hc.Y_pos]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_near_dihedral_identity (X Y s : ℝ) :
    (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ^ 2 +
        4 * s * Hpoly X Y s =
      (4 * s - (1 + s - Y) ^ 2) * (4 * s * X - (X + s - 1) ^ 2) := by
  unfold Hpoly
  ring

open HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_s_lt_four (hc : IsPathConfig c X Y s) : s < 4 := by
  have hx : dist (c 2) (c 1) ^ 2 = X := (p3_q_symm 2 1).trans hc.q12
  have hd21 : dist (c 2) (c 1) < 1 := by
    have hn := dist_nonneg (x := c 2) (y := c 1)
    nlinarith [hc.X_lt_one]
  have hd13 : dist (c 1) (c 3) = 1 := by
    have h13 : dist (c 1) (c 3) ^ 2 = 1 := hc.q13
    have hn := dist_nonneg (x := c 1) (y := c 3)
    nlinarith
  have hd23 : dist (c 2) (c 3) < 2 := by
    have ht := dist_triangle (c 2) (c 1) (c 3)
    linarith
  have hn := dist_nonneg (x := c 2) (y := c 3)
  have hs23 : dist (c 2) (c 3) ^ 2 = s := hc.q23
  nlinarith

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_q_pos_lt_four (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < q c i j ∧ q c i j < 4 := by
  have hs0 := p3_s_pos hc
  have hs4 := p3_s_lt_four hc
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change 0 < q c 0 1 ∧ q c 0 1 < 4
    rw [hc.q01]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 0 2 ∧ q c 0 2 < 4
    rw [hc.q02]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 0 3 ∧ q c 0 3 < 4
    rw [hc.q03]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 1 0 ∧ q c 1 0 < 4
    rw [p3_q_symm 1 0, hc.q01]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · exact (hij rfl).elim
  · change 0 < q c 1 2 ∧ q c 1 2 < 4
    rw [hc.q12]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 1 3 ∧ q c 1 3 < 4
    rw [hc.q13]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 2 0 ∧ q c 2 0 < 4
    rw [p3_q_symm 2 0, hc.q02]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 2 1 ∧ q c 2 1 < 4
    rw [p3_q_symm 2 1, hc.q12]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · exact (hij rfl).elim
  · change 0 < q c 2 3 ∧ q c 2 3 < 4
    rw [hc.q23]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 3 0 ∧ q c 3 0 < 4
    rw [p3_q_symm 3 0, hc.q03]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 3 1 ∧ q c 3 1 < 4
    rw [p3_q_symm 3 1, hc.q13]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 3 2 ∧ q c 3 2 < 4
    rw [p3_q_symm 3 2, hc.q23]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · exact (hij rfl).elim

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_radius_pos (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < Real.sqrt (1 - q c i j / 4) := by
  apply Real.sqrt_pos.2
  linarith [(p3_q_pos_lt_four hc i j hij).2]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_others (i j : Fin 4) (hij : i ≠ j) :
    oth1 i j ≠ i ∧ oth1 i j ≠ j ∧ oth2 i j ≠ i ∧
      oth2 i j ≠ j ∧ oth1 i j ≠ oth2 i j := by
  fin_cases i <;> fin_cases j <;> simp_all [oth1, oth2]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_indices_cover (i j m : Fin 4) (hij : i ≠ j) :
    m = i ∨ m = j ∨ m = oth1 i j ∨ m = oth2 i j := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all [oth1, oth2]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_locus_eq (c : Fin 4 → Pt) (i j : Fin 4) (hij : i ≠ j) :
    Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 ∩ Kset c =
      Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 ∩
        (Metric.closedBall (c (oth1 i j)) 1 ∩
          Metric.closedBall (c (oth2 i j)) 1) := by
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hijx, hK⟩
    refine ⟨hijx, ?_, ?_⟩
    · exact Set.mem_iInter.1 (Set.mem_iInter.1 hK (oth1 i j)) (Finset.mem_univ _)
    · exact Set.mem_iInter.1 (Set.mem_iInter.1 hK (oth2 i j)) (Finset.mem_univ _)
  · rintro ⟨⟨hix, hjx⟩, hkx, hlx⟩
    refine ⟨⟨hix, hjx⟩, ?_⟩
    apply Set.mem_iInter.2
    intro m
    apply Set.mem_iInter.2
    intro _
    rcases p3_indices_cover i j m hij with rfl | rfl | rfl | rfl
    · exact Metric.sphere_subset_closedBall hix
    · exact Metric.sphere_subset_closedBall hjx
    · exact hkx
    · exact hlx

open HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private def HardSphereB5.Lean.Geometry.PathCore.p3_nearBetaA (X Y s : ℝ) : ℝ :=
  atan2 (2 * Real.sqrt (Qpoly X Y s 1)) (Real.sqrt s * (1 + Y - s))
private def HardSphereB5.Lean.Geometry.PathCore.p3_nearBetaB (X Y s : ℝ) : ℝ :=
  atan2 (2 * Real.sqrt (Qpoly X Y s 0)) (Real.sqrt s * (1 + X - s))

private structure HardSphereB5.Lean.Geometry.PathCore.P3NearEndpointCounts (c : Fin 4 → Pt) (X Y s : ℝ) : Prop where
  bulk : 0 < P4poly X Y s → nRet c 1 = 1 ∧ nRet c 0 = 1
  nearA : P4poly X Y s < 0 → Y < X → nRet c 1 = 2 ∧ nRet c 0 = 0
  nearB : P4poly X Y s < 0 → X < Y → nRet c 1 = 0 ∧ nRet c 0 = 2

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_near_widths_of_pair23
    (hc : IsPathConfig c X Y s)
    (hCounts : P3NearEndpointCounts c X Y s)
    (hWidth : P4poly X Y s ≠ 0 →
      ell c 2 3 = (nRet c 1 : ℝ) * betaA c 2 3 0 +
        (nRet c 0 : ℝ) * betaA c 2 3 1 -
        (if 0 < P4poly X Y s then phiE c 2 3 else 0) -
        (if P4poly X Y s < 0 ∧ isCommon c 2 3 then 2 * Real.pi else 0)) :
    (0 < P4poly X Y s → ell c 2 3 =
      p3_nearBetaA X Y s + p3_nearBetaB X Y s - phiE c 2 3) ∧
    (P4poly X Y s < 0 → Y < X → ell c 2 3 = 2 * p3_nearBetaA X Y s) ∧
    (P4poly X Y s < 0 → X < Y → ell c 2 3 = 2 * p3_nearBetaB X Y s) := by
  have hA : betaA c 2 3 0 = p3_nearBetaA X Y s := p3_betaA_23_0 hc
  have hB : betaA c 2 3 1 = p3_nearBetaB X Y s := p3_betaA_23_1 hc
  refine ⟨?_, ?_, ?_⟩
  · intro hP
    rcases hCounts.bulk hP with ⟨hnA, hnB⟩
    have hW := hWidth (ne_of_gt hP)
    simpa [hnA, hnB, hA, hB, hP, not_lt_of_ge hP.le] using hW
  · intro hP hXY
    rcases hCounts.nearA hP hXY with ⟨hnA, hnB⟩
    have hNC : ¬ isCommon c 2 3 := by simp [isCommon, oth1, oth2, hnB]
    have hW := hWidth (ne_of_lt hP)
    simpa [hnA, hnB, hA, hB, hP, hNC, not_lt_of_ge hP.le] using hW
  · intro hP hXY
    rcases hCounts.nearB hP hXY with ⟨hnA, hnB⟩
    have hNC : ¬ isCommon c 2 3 := by simp [isCommon, oth1, oth2, hnA]
    have hW := hWidth (ne_of_lt hP)
    simpa [hnA, hnB, hA, hB, hP, hNC, not_lt_of_ge hP.le] using hW

open HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
open HardSphereB5.Lean (Pt)

private def HardSphereB5.Lean.Geometry.PathCore.p3_retainedTripleEndpoints (c : Fin 4 → Pt) (i j k l : Fin 4) : Set Pt :=
  {x | dist x (c i) = 1 ∧ dist x (c j) = 1 ∧
    dist x (c k) = 1 ∧ dist x (c l) ≤ 1}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_triple_retained_eq (c : Fin 4 → Pt) (i j : Fin 4) (hij : i ≠ j) :
    triplePts c (oth2 i j) ∩ Kset c =
      p3_retainedTripleEndpoints c i j (oth1 i j) (oth2 i j) := by
  have hp := p3_others i j hij
  ext x
  simp only [Set.mem_inter_iff, triplePts, Set.mem_setOf_eq,
    p3_retainedTripleEndpoints]
  constructor
  · rintro ⟨ht, hK⟩
    refine ⟨ht i hp.2.2.1.symm, ht j hp.2.2.2.1.symm,
      ht (oth1 i j) hp.2.2.2.2, ?_⟩
    exact Metric.mem_closedBall.1
      (Set.mem_iInter.1 (Set.mem_iInter.1 hK (oth2 i j)) (Finset.mem_univ _))
  · rintro ⟨hi, hj, hk, hl⟩
    have hK : x ∈ Kset c := by
      apply Set.mem_iInter.2
      intro m
      apply Set.mem_iInter.2
      intro _
      apply Metric.mem_closedBall.2
      rcases p3_indices_cover i j m hij with rfl | rfl | rfl | rfl
      · exact hi.le
      · exact hj.le
      · exact hk.le
      · exact hl
    refine ⟨?_, hK⟩
    intro m hm
    rcases p3_indices_cover i j m hij with rfl | rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
    · exact (hm rfl).elim

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_nRet_eq_endpoint_ncard (c : Fin 4 → Pt) (i j : Fin 4)
    (hij : i ≠ j) (hProper : 0 < Qface c (oth2 i j)) :
    nRet c (oth2 i j) =
      (p3_retainedTripleEndpoints c i j (oth1 i j) (oth2 i j)).ncard := by
  rw [nRet, if_pos hProper, p3_triple_retained_eq c i j hij]

open HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_atan2_range {y x : ℝ} (hy : 0 < y) :
    0 < atan2 y x ∧ atan2 y x < Real.pi := by
  have hnonneg : 0 ≤ Complex.arg (⟨x, y⟩ : ℂ) :=
    Complex.arg_nonneg_iff.mpr hy.le
  have hne : Complex.arg (⟨x, y⟩ : ℂ) ≠ 0 := by
    intro h
    have hzero := (Complex.arg_eq_zero_iff.mp h).2
    exact (ne_of_gt hy) hzero
  refine ⟨lt_of_le_of_ne hnonneg hne.symm, ?_⟩
  exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hy))

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_betaA_range (c : Fin 4 → Pt) (i j k : Fin 4)
    (hQ : 0 < Qf c i j k) :
    0 < betaA c i j k ∧ betaA c i j k < Real.pi := by
  apply p3_atan2_range
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hQ)

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_near_betaA_acute (hc : IsPathConfig c X Y s) (hs : s < 1) :
    betaA c 2 3 0 < Real.pi / 2 ∧ betaA c 2 3 1 < Real.pi / 2 := by
  have hr := Real.sqrt_pos.mpr (p3_s_pos hc)
  have hp := p3_near_numerators_pos hc hs
  rw [p3_betaA_23_0 hc, p3_betaA_23_1 hc]
  constructor
  · exact Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (mul_pos hr hp.1))
  · exact Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (mul_pos hr hp.2))

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_ball_cut (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (hd : dist (c i) (c j) < 2) (t : ℝ) :
    SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.closedBall (c k) 1 ↔
      q c i k + q c j k - q c i j ≤
        4 * Real.sqrt (1 - q c i j / 4) *
          (Real.cos t * inner ℝ (e 0) (c k - c i) +
            Real.sin t * inner ℝ (e 1) (c k - c i)) := by
  have hp := CircleArc.pair_circle_on_spheres (c i) (c j) e he hperp hd t
  change SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
    (Real.sqrt (1 - q c i j / 4)) t ∈ _ ∩ _ at hp
  rw [CircleArc.ball_iff_inner (c i) (c k) _ hp.1]
  have hinner := near_inner_from_q c i j k
  have hx : SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t - c i =
      (1 / 2 : ℝ) • (c j - c i) + Real.sqrt (1 - q c i j / 4) •
        (Real.cos t • e 0 + Real.sin t • e 1) := by
    unfold SphereGeom.circlePt
    module
  rw [hx]
  simp only [inner_add_left, real_inner_smul_left]
  change q c i k / 2 ≤ _ ↔ _
  constructor <;> intro h <;> nlinarith [hinner]

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_ell_from_interval_chart (hc : IsPathConfig c X Y s)
    (i j : Fin 4) (hij : i ≠ j) (m : Pt) (e : Fin 2 → Pt)
    (he : Orthonormal ℝ e) (a b : ℝ) (hab : a ≤ b)
    (hspan : b - a ≤ 2 * Real.pi)
    (hchart : Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 ∩ Kset c =
      SphereGeom.circlePt m (e 0) (e 1) (Real.sqrt (1 - q c i j / 4)) '' Set.Icc a b) :
    ell c i j = b - a := by
  have hr := p3_pair_radius_pos hc i j hij
  unfold ell
  rw [hchart, SphereGeom.arcMeasure_circle_arc m e he _ hr a b hab hspan,
    ENNReal.toReal_ofReal (mul_nonneg hr.le (sub_nonneg.mpr hab))]
  exact mul_div_cancel_left₀ (b - a) (ne_of_gt hr)

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_near_moving_point_width_of_pair23
    (hc : IsPathConfig c X Y s) (hs : s < 1)
    (hCounts : P3NearEndpointCounts c X Y s)
    (hWidth : P4poly X Y s ≠ 0 →
      ell c 2 3 = (nRet c 1 : ℝ) * betaA c 2 3 0 +
        (nRet c 0 : ℝ) * betaA c 2 3 1 -
        (if 0 < P4poly X Y s then phiE c 2 3 else 0) -
        (if P4poly X Y s < 0 ∧ isCommon c 2 3 then 2 * Real.pi else 0)) :
    phiE c 2 3 = atan2 (2 * Real.sqrt (s * Hpoly X Y s))
        (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ∧
    (0 < P4poly X Y s → ell c 2 3 =
      atan2 (2 * Real.sqrt (Qpoly X Y s 1)) (Real.sqrt s * (1 + Y - s)) +
        atan2 (2 * Real.sqrt (Qpoly X Y s 0)) (Real.sqrt s * (1 + X - s)) - phiE c 2 3) ∧
    (P4poly X Y s < 0 → Y < X → ell c 2 3 =
      2 * atan2 (2 * Real.sqrt (Qpoly X Y s 1)) (Real.sqrt s * (1 + Y - s))) ∧
    (P4poly X Y s < 0 → X < Y → ell c 2 3 =
      2 * atan2 (2 * Real.sqrt (Qpoly X Y s 0)) (Real.sqrt s * (1 + X - s))) := by
  refine ⟨near_moving_point_angle hc hs, ?_⟩
  exact p3_near_widths_of_pair23 hc hCounts hWidth

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_Qface_eq (c : Fin 4 → Pt) (i j : Fin 4) (hij : i ≠ j) :
    Qf c i j (oth1 i j) = Qface c (oth2 i j) ∧
      Qf c i j (oth2 i j) = Qface c (oth1 i j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [oth1, oth2, Qface, faceVerts, Qf, QT, DeltaT, q] <;>
    simp only [dist_comm (c 1) (c 0), dist_comm (c 2) (c 0), dist_comm (c 3) (c 0),
      dist_comm (c 2) (c 1), dist_comm (c 3) (c 1), dist_comm (c 3) (c 2)] <;> first | trivial | (constructor <;> ring) | ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_Q_pos (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    0 < Qf c i j (oth1 i j) ∧ 0 < Qf c i j (oth2 i j) := by
  have hQ : ∀ l, 0 < Qface c l := by
    intro l
    rw [(face_polys c X Y s hc l).1]
    exact path_Qpoly_pos c X Y s hc l
  rw [(p3_pair_Qface_eq c i j hij).1, (p3_pair_Qface_eq c i j hij).2]
  exact ⟨hQ _, hQ _⟩

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_gram_poly (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    gramPoly (q c i j) (q c i (oth1 i j)) (q c j (oth1 i j))
      (q c i (oth2 i j)) (q c j (oth2 i j)) (q c (oth1 i j) (oth2 i j)) =
        Hpoly X Y s := by
  have h10 : q c 1 0 = 1 := by rw [q_symm', hc.q01]
  have h20 : q c 2 0 = 1 := by rw [q_symm', hc.q02]
  have h30 : q c 3 0 = Y := by rw [q_symm', hc.q03]
  have h21 : q c 2 1 = X := by rw [q_symm', hc.q12]
  have h31 : q c 3 1 = 1 := by rw [q_symm', hc.q13]
  have h32 : q c 3 2 = s := by rw [q_symm', hc.q23]
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals simp [oth1, oth2, hc.q01, hc.q02, hc.q03, hc.q12, hc.q13,
    hc.q23, h10, h20, h30, h21, h31, h32, gramPoly, Hpoly] <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_perpProj_perp (v w : Pt) (hv : inner ℝ v v ≠ 0) :
    inner ℝ v (perpProj v w) = 0 := by
  simp only [perpProj, inner_sub_right, real_inner_smul_right]
  rw [real_inner_comm w v]
  field_simp [hv]
  <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_projected_gram (v w z : Pt) (hv : inner ℝ v v ≠ 0) :
    inner ℝ v v *
      (‖perpProj v w‖ ^ 2 * ‖perpProj v z‖ ^ 2 -
        (inner ℝ (perpProj v w) (perpProj v z)) ^ 2) =
      (inner ℝ (SphereGeom.cross v w) z) ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, near_perpProj_inner _ _ _ hv,
    cross_gram_identity]
  rw [real_inner_comm w v, real_inner_comm z v]
  field_simp [hv]
  <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_projected_gram_pos (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) :
    0 < ‖perpProj (c j - c i) (c (oth1 i j) - c i)‖ ^ 2 *
        ‖perpProj (c j - c i) (c (oth2 i j) - c i)‖ ^ 2 -
      (inner ℝ (perpProj (c j - c i) (c (oth1 i j) - c i))
        (perpProj (c j - c i) (c (oth2 i j) - c i))) ^ 2 := by
  have hq := (p3_q_pos_lt_four hc i j hij).1
  have hv : 0 < inner ℝ (c j - c i) (c j - c i) := by rwa [← q_inner]
  have hg := gram_from_q c i j (oth1 i j) (oth2 i j)
  rw [p3_pair_gram_poly hc i j hij] at hg
  have hd : 0 < (inner ℝ (SphereGeom.cross (c j - c i) (c (oth1 i j) - c i))
      (c (oth2 i j) - c i)) ^ 2 := by linarith [hc.H_pos]
  have he := p3_projected_gram (c j - c i) (c (oth1 i j) - c i)
    (c (oth2 i j) - c i) (ne_of_gt hv)
  apply (mul_pos_iff_of_pos_left hv).mp
  rwa [he]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_phi_range (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    0 < phiE c i j ∧ phiE c i j < Real.pi := by
  let u := perpProj (c j - c i) (c (oth1 i j) - c i)
  let v := perpProj (c j - c i) (c (oth2 i j) - c i)
  let G := ‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2
  have hG : 0 < G := p3_pair_projected_gram_pos hc i j hij
  have hy := Real.sqrt_pos.mpr hG
  have hi : (1 : ℝ) * inner ℝ u v = inner ℝ u v := one_mul _
  have hg : (1 : ℝ) ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) =
      (inner ℝ u v) ^ 2 + (Real.sqrt G) ^ 2 := by
    rw [Real.sq_sqrt hG.le]
    dsimp [G]
    ring
  have ha := InnerAngle.angle_eq_arg_of_scaled_gram u v 1 _ _ (by norm_num) hy hi hg
  change 0 < InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v < Real.pi
  rw [ha]
  exact p3_atan2_range hy

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_aligned_frame (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    ∃ e : Fin 2 → Pt, Orthonormal ℝ e ∧
      (∀ n, inner ℝ (c j - c i) (e n) = 0) ∧
      perpProj (c j - c i) (c (oth1 i j) - c i) =
        ‖perpProj (c j - c i) (c (oth1 i j) - c i)‖ • e 0 ∧
      perpProj (c j - c i) (c (oth2 i j) - c i) =
        ‖perpProj (c j - c i) (c (oth2 i j) - c i)‖ •
          (Real.cos (phiE c i j) • e 0 + Real.sin (phiE c i j) • e 1) := by
  let u := perpProj (c j - c i) (c (oth1 i j) - c i)
  let v := perpProj (c j - c i) (c (oth2 i j) - c i)
  have hG : 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 :=
    p3_pair_projected_gram_pos hc i j hij
  obtain ⟨f, hf, hu, hv⟩ := SphereGeom.pair_normalized_frame u v hG
  let e : Fin 2 → Pt := fun n => f (Fin.castLE (by decide : 2 ≤ 3) n)
  have he : Orthonormal ℝ e := hf.comp _ (Fin.castLE_injective _)
  have huo : 0 < ‖u‖ := by
    by_contra h
    have hz : ‖u‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz] at hG
    nlinarith [sq_nonneg (inner ℝ u v)]
  have hvo : 0 < ‖v‖ := by
    by_contra h
    have hz : ‖v‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz] at hG
    nlinarith [sq_nonneg (inner ℝ u v)]
  have hvv : inner ℝ (c j - c i) (c j - c i) ≠ 0 := by
    rw [← q_inner]
    exact ne_of_gt (p3_q_pos_lt_four hc i j hij).1
  have hpu := p3_perpProj_perp (c j - c i) (c (oth1 i j) - c i) hvv
  have hpv := p3_perpProj_perp (c j - c i) (c (oth2 i j) - c i) hvv
  have hsin := Real.sin_pos_of_pos_of_lt_pi (p3_phi_range hc i j hij).1
    (p3_phi_range hc i j hij).2
  change u = ‖u‖ • e 0 at hu
  change v = ‖v‖ • (Real.cos (phiE c i j) • e 0 +
    Real.sin (phiE c i j) • e 1) at hv
  have hp0 : inner ℝ (c j - c i) (e 0) = 0 := by
    change inner ℝ (c j - c i) u = 0 at hpu
    rw [hu, real_inner_smul_right] at hpu
    exact (mul_eq_zero.mp hpu).resolve_left (ne_of_gt huo)
  have hp1 : inner ℝ (c j - c i) (e 1) = 0 := by
    change inner ℝ (c j - c i) v = 0 at hpv
    rw [hv, real_inner_smul_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, hp0] at hpv
    simp only [mul_zero, zero_add] at hpv
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hpv).resolve_left (ne_of_gt hvo))).resolve_left
      (ne_of_gt hsin)
  refine ⟨e, he, ?_, hu, hv⟩
  intro n
  fin_cases n
  · exact hp0
  · exact hp1

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_near_counts (hc : IsPathConfig c X Y s) (hs : s < 1) :
    P3NearEndpointCounts c X Y s := by
  refine ⟨?_, ?_, ?_⟩
  · intro hP
    exact ⟨(bulk_incidence hc hP).1 1, (bulk_incidence hc hP).1 0⟩
  · intro hP hYX
    have h := ((sliver_table hc hP).1 hs hYX).1
    have h1 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.1) h
    have h0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.2) h
    exact ⟨h1, h0⟩
  · intro hP hXY
    have h := ((sliver_table hc hP).2.1 hs hXY).1
    have h1 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.1) h
    have h0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.2) h
    exact ⟨h1, h0⟩

noncomputable section
open SphereGeom
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000

open CircleArc

private theorem CircleArc.pair_circle_on_spheres_source (a b : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (hperp : ∀ i, inner ℝ (b - a) (e i) = 0)
    (hd : dist a b < 2) (t : ℝ) :
    circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1)
      (Real.sqrt (1 - dist a b ^ 2 / 4)) t ∈ Metric.sphere a 1 ∩ Metric.sphere b 1 := by
  let r : ℝ := Real.sqrt (1 - dist a b ^ 2 / 4)
  let u : E3 := Real.cos t • e 0 + Real.sin t • e 1
  have he00 : inner ℝ (e 0) (e 0) = 1 := by
    rw [real_inner_self_eq_norm_sq, he.1 0]; norm_num
  have he11 : inner ℝ (e 1) (e 1) = 1 := by
    rw [real_inner_self_eq_norm_sq, he.1 1]; norm_num
  have he01 : inner ℝ (e 0) (e 1) = 0 := he.inner_eq_zero (by decide)
  have he10 : inner ℝ (e 1) (e 0) = 0 := he.inner_eq_zero (by decide)
  have hu : inner ℝ u u = 1 := by
    dsimp [u]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, he00, he11, he01, he10]
    nlinarith [Real.cos_sq_add_sin_sq t]
  have hvu : inner ℝ (b - a) u = 0 := by
    simp [u, inner_add_right, real_inner_smul_right, hperp]
  have huv : inner ℝ u (b - a) = 0 := by
    rw [real_inner_comm]; exact hvu
  have hv : inner ℝ (b - a) (b - a) = dist a b ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm]
  have hr : r ^ 2 = 1 - dist a b ^ 2 / 4 := by
    apply Real.sq_sqrt
    nlinarith [dist_nonneg (x := a) (y := b)]
  have hxa : circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a =
      (1 / 2 : ℝ) • (b - a) + r • u := by
    dsimp [circlePt, u]; module
  have hxb : circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b =
      (-1 / 2 : ℝ) • (b - a) + r • u := by
    dsimp [circlePt, u]; module
  have hna : ‖circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hxa]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvu, huv, hv, hu]
    nlinarith [hr]
  have hnb : ‖circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hxb]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvu, huv, hv, hu]
    nlinarith [hr]
  constructor <;> rw [Metric.mem_sphere, dist_eq_norm]
  · nlinarith [norm_nonneg (circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a)]
  · nlinarith [norm_nonneg (circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b)]

private theorem CircleArc.frame_expansion (e : Fin 3 → E3) (he : Orthonormal ℝ e) (x : E3) :
    x = inner ℝ (e 0) x • e 0 + inner ℝ (e 1) x • e 1 +
      inner ℝ (e 2) x • e 2 := by
  have hspan : Submodule.span ℝ (Set.range e) = ⊤ :=
    he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])
  let B : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk he hspan.ge
  have h := B.sum_repr' x
  simpa [B, Fin.sum_univ_succ, add_assoc] using h.symm

private theorem CircleArc.exists_polar_angle_Icc (u v r : ℝ) (hr : 0 ≤ r) (hsq : u ^ 2 + v ^ 2 = r ^ 2) :
    ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), r * Real.cos t = u ∧ r * Real.sin t = v := by
  let z : ℂ := ⟨u, v⟩
  have hzsq : ‖z‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [z, Complex.normSq_apply, pow_two] using hsq
  have hz : ‖z‖ = r := by nlinarith [norm_nonneg z]
  have hc : r * Real.cos (Complex.arg z) = u := by
    simpa [hz, z] using Complex.norm_mul_cos_arg z
  have hs : r * Real.sin (Complex.arg z) = v := by
    simpa [hz, z] using Complex.norm_mul_sin_arg z
  by_cases ht : 0 ≤ Complex.arg z
  · refine ⟨Complex.arg z, ⟨ht, ?_⟩, hc, hs⟩
    linarith [Complex.arg_le_pi z, Real.pi_pos]
  · refine ⟨Complex.arg z + 2 * Real.pi, ⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
    · linarith [lt_of_not_ge ht]
    · simpa only [Real.cos_add_two_pi] using hc
    · simpa only [Real.sin_add_two_pi] using hs

private theorem CircleArc.pair_circle_on_spheres_frame (a b : E3) (e : Fin 3 → E3)
    (he : Orthonormal ℝ e) (haxis : b - a = ‖b - a‖ • e 0)
    (hd : dist a b < 2) (t : ℝ) :
    circlePt ((1 / 2 : ℝ) • (a + b)) (e 1) (e 2)
      (Real.sqrt (1 - dist a b ^ 2 / 4)) t ∈ Metric.sphere a 1 ∩ Metric.sphere b 1 := by
  let f : Fin 2 → E3 := fun i => e i.succ
  have hf : Orthonormal ℝ f := he.comp Fin.succ (Fin.succ_injective 2)
  have hp : ∀ i : Fin 2, inner ℝ (b - a) (f i) = 0 := by
    intro i
    change inner ℝ (b - a) (e i.succ) = 0
    have he0i : inner ℝ (e 0) (e i.succ) = 0 :=
      he.inner_eq_zero (Fin.succ_ne_zero i).symm
    rw [haxis, real_inner_smul_left, he0i]
    simp
  simpa [f] using pair_circle_on_spheres_source a b f hf hp hd t

private theorem CircleArc.pair_sphere_chart (a b : E3) (e : Fin 3 → E3)
    (he : Orthonormal ℝ e) (haxis : b - a = ‖b - a‖ • e 0)
    (hd0 : 0 < dist a b) (hd2 : dist a b < 2) :
    Metric.sphere a 1 ∩ Metric.sphere b 1 =
      circlePt ((1 / 2 : ℝ) • (a + b)) (e 1) (e 2)
        (Real.sqrt (1 - dist a b ^ 2 / 4)) '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
  let m : E3 := (1 / 2 : ℝ) • (a + b)
  let r : ℝ := Real.sqrt (1 - dist a b ^ 2 / 4)
  have hnv : ‖b - a‖ = dist a b := by rw [← dist_eq_norm, dist_comm]
  have hnvpos : 0 < ‖b - a‖ := by rwa [hnv]
  have hv : inner ℝ (b - a) (b - a) = dist a b ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hnv]
  have hr : r ^ 2 = 1 - dist a b ^ 2 / 4 := by
    apply Real.sq_sqrt
    nlinarith
  ext x
  constructor
  · intro hx
    let y : E3 := x - m
    have hxa : ‖x - a‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hx.1
    have hxb : ‖x - b‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hx.2
    have hva : x - a = y + (1 / 2 : ℝ) • (b - a) := by dsimp [y, m]; module
    have hvb : x - b = y + (-1 / 2 : ℝ) • (b - a) := by dsimp [y, m]; module
    have hvy : inner ℝ (b - a) y = inner ℝ y (b - a) := real_inner_comm _ _
    have hA : inner ℝ y y + inner ℝ y (b - a) + dist a b ^ 2 / 4 = 1 := by
      have h := congrArg (fun z : ℝ => z ^ 2) hxa
      rw [← real_inner_self_eq_norm_sq, hva] at h
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hvy, hv] at h
      nlinarith [h]
    have hB : inner ℝ y y - inner ℝ y (b - a) + dist a b ^ 2 / 4 = 1 := by
      have h := congrArg (fun z : ℝ => z ^ 2) hxb
      rw [← real_inner_self_eq_norm_sq, hvb] at h
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hvy, hv] at h
      nlinarith [h]
    have hyaxis : inner ℝ y (b - a) = 0 := by linarith
    have hynorm : inner ℝ y y = r ^ 2 := by linarith
    have hy0 : inner ℝ (e 0) y = 0 := by
      rw [real_inner_comm]
      rw [haxis, real_inner_smul_right] at hyaxis
      nlinarith
    have hyrepr : y = inner ℝ (e 1) y • e 1 + inner ℝ (e 2) y • e 2 := by
      simpa only [hy0, zero_smul, zero_add] using frame_expansion e he y
    have he11 : inner ℝ (e 1) (e 1) = 1 := by
      rw [real_inner_self_eq_norm_sq, he.norm_eq_one 1]; norm_num
    have he22 : inner ℝ (e 2) (e 2) = 1 := by
      rw [real_inner_self_eq_norm_sq, he.norm_eq_one 2]; norm_num
    have he12 : inner ℝ (e 1) (e 2) = 0 := he.inner_eq_zero (by decide)
    have he21 : inner ℝ (e 2) (e 1) = 0 := he.inner_eq_zero (by decide)
    have hcoords : (inner ℝ (e 1) y) ^ 2 + (inner ℝ (e 2) y) ^ 2 = r ^ 2 := by
      have h := congrArg (fun z : E3 => inner ℝ z z) hyrepr
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he11, he22, he12, he21] at h
      nlinarith [h]
    obtain ⟨t, ht, hc, hs⟩ := exists_polar_angle_Icc (inner ℝ (e 1) y)
      (inner ℝ (e 2) y) r (Real.sqrt_nonneg _) hcoords
    refine ⟨t, ht, ?_⟩
    change circlePt m (e 1) (e 2) r t = x
    simp only [circlePt, smul_add, smul_smul, hc, hs]
    rw [← hyrepr]
    dsimp [y]
    abel
  · rintro ⟨t, ht, rfl⟩
    exact pair_circle_on_spheres_frame a b e he haxis hd2 t

private theorem CircleArc.pair_sphere_chart_two (a b : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (hperp : ∀ i, inner ℝ (b - a) (e i) = 0)
    (hd0 : 0 < dist a b) (hd2 : dist a b < 2) :
    Metric.sphere a 1 ∩ Metric.sphere b 1 =
      circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1)
        (Real.sqrt (1 - dist a b ^ 2 / 4)) '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hvpos : 0 < ‖b - a‖ := by rw [← dist_eq_norm, dist_comm]; exact hd0
  let n : E3 := ‖b - a‖⁻¹ • (b - a)
  have hn : ‖n‖ = 1 := by
    simp [n, norm_smul, Real.norm_eq_abs, abs_of_pos hvpos, ne_of_gt hvpos]
  have heeq : (![e 0, e 1] : Fin 2 → E3) = e := by
    funext i; fin_cases i <;> rfl
  let f : Fin 3 → E3 := ![n, e 0, e 1]
  have hf : Orthonormal ℝ f := by
    change Orthonormal ℝ (Matrix.vecCons n ![e 0, e 1])
    rw [orthonormal_vecCons_iff]
    refine ⟨hn, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [n, real_inner_smul_left, hperp]
    · rwa [heeq]
  have haxis : b - a = ‖b - a‖ • f 0 := by
    change b - a = ‖b - a‖ • (‖b - a‖⁻¹ • (b - a))
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
  simpa [f] using pair_sphere_chart a b f hf haxis hd0 hd2

noncomputable section
open CircleArc

private theorem CircleArc.cos_cut_periodic (β t : ℝ) (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Real.cos β ≤ Real.cos t ↔
      ∃ n : ℤ, t ∈ Set.Icc (-β + 2 * Real.pi * n) (β + 2 * Real.pi * n) := by
  constructor
  · intro hcos
    let u : ℝ := (t : Real.Angle).toReal
    have hup : |u| ≤ Real.pi := Real.Angle.abs_toReal_le_pi _
    have hcosu : Real.cos |u| = Real.cos t := by
      rw [Real.cos_abs]
      exact (Real.Angle.cos_toReal (t : Real.Angle)).trans (Real.Angle.cos_coe t)
    have hab : |u| ≤ β := by
      by_contra h
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hβ0 hup (lt_of_not_ge h)
      rw [hcosu] at hc
      exact (not_lt_of_ge hcos) hc
    obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.coe_toReal (t : Real.Angle)).symm
    refine ⟨n, ?_, ?_⟩ <;> linarith [(abs_le.mp hab).1, (abs_le.mp hab).2]
  · rintro ⟨n, hnlo, hnhi⟩
    have hab : |t - (n : ℝ) * (2 * Real.pi)| ≤ β := by
      apply abs_le.mpr
      constructor <;> nlinarith
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      hβπ hab
    rw [Real.cos_abs, Real.cos_sub_int_mul_two_pi] at hcos
    exact hcos

private theorem CircleArc.cos_cut_periodic_shift (β θ t : ℝ) (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Real.cos β ≤ Real.cos (t - θ) ↔
      ∃ n : ℤ, t ∈ Set.Icc (θ - β + 2 * Real.pi * n) (θ + β + 2 * Real.pi * n) := by
  rw [cos_cut_periodic β (t - θ) hβ0 hβπ]
  constructor <;> rintro ⟨n, hlo, hhi⟩ <;> refine ⟨n, ?_, ?_⟩ <;> linarith

private theorem CircleArc.cos_endpoint_periodic_shift (β θ t : ℝ) :
    Real.cos (t - θ) = Real.cos β ↔
      ∃ n : ℤ, t = θ + β + 2 * Real.pi * n ∨ t = θ - β + 2 * Real.pi * n := by
  rw [eq_comm, Real.cos_eq_cos_iff]
  constructor <;> rintro ⟨n, hp | hm⟩
  · exact ⟨n, Or.inl (by nlinarith)⟩
  · exact ⟨n, Or.inr (by nlinarith)⟩
  · exact ⟨n, Or.inl (by nlinarith)⟩
  · exact ⟨n, Or.inr (by nlinarith)⟩

private theorem CircleArc.phase_cos (x y t : ℝ) (hz : (⟨x,y⟩ : ℂ) ≠ 0) :
    x * Real.cos t + y * Real.sin t =
      ‖(⟨x,y⟩ : ℂ)‖ * Real.cos (t - Complex.arg ⟨x,y⟩) := by
  rw [Real.cos_sub, Complex.cos_arg hz, Complex.sin_arg]
  change x * Real.cos t + y * Real.sin t =
    ‖(⟨x,y⟩ : ℂ)‖ * (Real.cos t * (x / ‖(⟨x,y⟩ : ℂ)‖) +
      Real.sin t * (y / ‖(⟨x,y⟩ : ℂ)‖))
  field_simp [norm_ne_zero_iff.mpr hz]
  <;> ring

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_projection_sq_from_q (c : Fin 4 → Pt) (i j k : Fin 4)
    (ha : 0 < q c i j) :
    4 * q c i j * ‖perpProj (c j - c i) (c k - c i)‖ ^ 2 = Deltaf c i j k := by
  have hv : inner ℝ (c j - c i) (c j - c i) = q c i j := by
    rw [real_inner_self_eq_norm_sq, near_norm_sub_q, near_q_symm]
  have hw : inner ℝ (c k - c i) (c k - c i) = q c i k := by
    rw [real_inner_self_eq_norm_sq, near_norm_sub_q, near_q_symm]
  have hv0 : inner ℝ (c j - c i) (c j - c i) ≠ 0 := by rw [hv]; exact ne_of_gt ha
  have hh := near_inner_from_q c i j k
  rw [real_inner_comm] at hh
  have hi : inner ℝ (c k - c i) (c j - c i) =
      (q c i j + q c i k - q c j k) / 2 := by linarith
  rw [← real_inner_self_eq_norm_sq, near_perpProj_inner _ _ _ hv0, hv, hw, hi]
  unfold Deltaf DeltaT
  field_simp [ne_of_gt ha]
  <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_beta_complex_norm (c : Fin 4 → Pt) (i j k : Fin 4)
    (ha : 0 < q c i j) (ha4 : q c i j < 4) (hQ : 0 < Qf c i j k) :
    ‖(⟨Real.sqrt (q c i j) * (q c i k + q c j k - q c i j),
      2 * Real.sqrt (Qf c i j k)⟩ : ℂ)‖ =
      4 * Real.sqrt (q c i j) * Real.sqrt (1 - q c i j / 4) *
        ‖perpProj (c j - c i) (c k - c i)‖ := by
  have hr : 0 ≤ 1 - q c i j / 4 := by linarith
  have hp := p3_projection_sq_from_q c i j k ha
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [← Complex.normSq_eq_norm_sq]
  change (Real.sqrt (q c i j) * (q c i k + q c j k - q c i j)) *
      (Real.sqrt (q c i j) * (q c i k + q c j k - q c i j)) +
    (2 * Real.sqrt (Qf c i j k)) * (2 * Real.sqrt (Qf c i j k)) = _
  calc
    _ = (Real.sqrt (q c i j)) ^ 2 * (q c i k + q c j k - q c i j) ^ 2 +
        4 * (Real.sqrt (Qf c i j k)) ^ 2 := by ring
    _ = q c i j * (q c i k + q c j k - q c i j) ^ 2 + 4 * Qf c i j k := by
      rw [Real.sq_sqrt ha.le, Real.sq_sqrt hQ.le]
    _ = (4 - q c i j) * Deltaf c i j k := by unfold Qf QT Deltaf DeltaT; ring
    _ = (4 - q c i j) *
        (4 * q c i j * ‖perpProj (c j - c i) (c k - c i)‖ ^ 2) := by rw [hp]
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hr]
      ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_beta_cos_ratio (c : Fin 4 → Pt) (i j k : Fin 4)
    (ha : 0 < q c i j) (ha4 : q c i j < 4) (hQ : 0 < Qf c i j k) :
    0 < ‖perpProj (c j - c i) (c k - c i)‖ ∧
    Real.cos (betaA c i j k) = (q c i k + q c j k - q c i j) /
      (4 * Real.sqrt (1 - q c i j / 4) * ‖perpProj (c j - c i) (c k - c i)‖) := by
  let z : ℂ := ⟨Real.sqrt (q c i j) * (q c i k + q c j k - q c i j),
      2 * Real.sqrt (Qf c i j k)⟩
  have hz : z ≠ 0 := by
    intro heq
    have hi := congrArg Complex.im heq
    change 2 * Real.sqrt (Qf c i j k) = 0 at hi
    have hsq := Real.sqrt_pos.mpr hQ
    linarith
  have hn := p3_beta_complex_norm c i j k ha ha4 hQ
  have hp : 0 < ‖perpProj (c j - c i) (c k - c i)‖ := by
    have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    change 0 < ‖(⟨Real.sqrt (q c i j) * (q c i k + q c j k - q c i j),
      2 * Real.sqrt (Qf c i j k)⟩ : ℂ)‖ at hzp
    rw [hn] at hzp
    by_contra h
    have hp0 : ‖perpProj (c j - c i) (c k - c i)‖ = 0 :=
      le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hp0, mul_zero] at hzp
    exact lt_irrefl _ hzp
  refine ⟨hp, ?_⟩
  change Real.cos z.arg = _
  rw [Complex.cos_arg hz]
  change (Real.sqrt (q c i j) * (q c i k + q c j k - q c i j)) /
    ‖(⟨Real.sqrt (q c i j) * (q c i k + q c j k - q c i j),
      2 * Real.sqrt (Qf c i j k)⟩ : ℂ)‖ = _
  rw [hn]
  have hs : Real.sqrt (q c i j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hr : Real.sqrt (1 - q c i j / 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  field_simp [hs, hr, ne_of_gt hp]
  <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_projection_phase_norm (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hframe : perpProj (c j - c i) (c k - c i) =
      inner ℝ (e 0) (c k - c i) • e 0 + inner ℝ (e 1) (c k - c i) • e 1) :
    ‖(⟨inner ℝ (e 0) (c k - c i), inner ℝ (e 1) (c k - c i)⟩ : ℂ)‖ =
      ‖perpProj (c j - c i) (c k - c i)‖ := by
  have he00 : inner ℝ (e 0) (e 0) = 1 := by simpa using (orthonormal_iff_ite.mp he) 0 0
  have he01 : inner ℝ (e 0) (e 1) = 0 := by simpa using (orthonormal_iff_ite.mp he) 0 1
  have he10 : inner ℝ (e 1) (e 0) = 0 := by simpa using (orthonormal_iff_ite.mp he) 1 0
  have he11 : inner ℝ (e 1) (e 1) = 1 := by simpa using (orthonormal_iff_ite.mp he) 1 1
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← real_inner_self_eq_norm_sq, hframe]
  simp only [Complex.normSq_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, he00, he01, he10, he11]
  ring

open CircleArc

private theorem CircleArc.sphere_iff_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a k x : V) (hx : x ∈ Metric.sphere a 1) :
    x ∈ Metric.sphere k 1 ↔ dist a k ^ 2 / 2 = inner ℝ (x - a) (k - a) := by
  have hxa : ‖x - a‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  have hw : ‖k - a‖ = dist a k := by rw [← dist_eq_norm, dist_comm]
  have hvec : x - k = (x - a) - (k - a) := by abel
  have hsq : dist x k ^ 2 = 1 - 2 * inner ℝ (x - a) (k - a) + dist a k ^ 2 := by
    rw [dist_eq_norm, hvec, norm_sub_sq_real, hxa, hw]; norm_num
  rw [Metric.mem_sphere]
  constructor <;> intro h <;> nlinarith [dist_nonneg (x := x) (y := k)]

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_sphere_cut (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (hd : dist (c i) (c j) < 2) (t : ℝ) :
    SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.sphere (c k) 1 ↔
      q c i k + q c j k - q c i j =
        4 * Real.sqrt (1 - q c i j / 4) *
          (Real.cos t * inner ℝ (e 0) (c k - c i) +
            Real.sin t * inner ℝ (e 1) (c k - c i)) := by
  have hp := CircleArc.pair_circle_on_spheres (c i) (c j) e he hperp hd t
  change SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
    (Real.sqrt (1 - q c i j / 4)) t ∈ _ ∩ _ at hp
  rw [CircleArc.sphere_iff_inner (c i) (c k) _ hp.1]
  have hinner := near_inner_from_q c i j k
  have hx : SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t - c i =
      (1 / 2 : ℝ) • (c j - c i) + Real.sqrt (1 - q c i j / 4) •
        (Real.cos t • e 0 + Real.sin t • e 1) := by
    unfold SphereGeom.circlePt
    module
  rw [hx]
  simp only [inner_add_left, real_inner_smul_left]
  change q c i k / 2 = _ ↔ _
  constructor <;> intro h <;> nlinarith [hinner]

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_ball_beta_shift (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (hframe : perpProj (c j - c i) (c k - c i) =
      inner ℝ (e 0) (c k - c i) • e 0 + inner ℝ (e 1) (c k - c i) • e 1)
    (ha : 0 < q c i j) (hd : dist (c i) (c j) < 2)
    (hQ : 0 < Qf c i j k) (t : ℝ) :
    SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.closedBall (c k) 1 ↔
      ∃ n : ℤ, t ∈ Set.Icc
        (Complex.arg ⟨inner ℝ (e 0) (c k - c i), inner ℝ (e 1) (c k - c i)⟩ -
          betaA c i j k + 2 * Real.pi * n)
        (Complex.arg ⟨inner ℝ (e 0) (c k - c i), inner ℝ (e 1) (c k - c i)⟩ +
          betaA c i j k + 2 * Real.pi * n) := by
  have ha4 : q c i j < 4 := by unfold q; nlinarith [dist_nonneg (x := c i) (y := c j)]
  rcases p3_beta_cos_ratio c i j k ha ha4 hQ with ⟨hp, hβ⟩
  have hpn := p3_projection_phase_norm c i j k e he hframe
  have hz : (⟨inner ℝ (e 0) (c k - c i), inner ℝ (e 1) (c k - c i)⟩ : ℂ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hpn]
    exact ne_of_gt hp
  have hcoeff := CircleArc.phase_cos (inner ℝ (e 0) (c k - c i))
    (inner ℝ (e 1) (c k - c i)) t hz
  rw [hpn] at hcoeff
  have hR : 0 < 4 * Real.sqrt (1 - q c i j / 4) *
      ‖perpProj (c j - c i) (c k - c i)‖ := by
    apply mul_pos _ hp
    apply mul_pos (by norm_num)
    apply Real.sqrt_pos.mpr
    linarith
  rw [p3_pair_circle_ball_cut c i j k e he hperp hd t]
  rw [← CircleArc.cos_cut_periodic_shift (betaA c i j k) _ t
    (p3_betaA_range c i j k hQ).1.le (p3_betaA_range c i j k hQ).2.le]
  rw [hβ, div_le_iff₀ hR]
  have hcoeff' := congrArg (fun r : ℝ => 4 * Real.sqrt (1 - q c i j / 4) * r) hcoeff
  constructor <;> intro h <;> nlinarith [hcoeff']

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_sphere_beta_shift (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (hframe : perpProj (c j - c i) (c k - c i) =
      inner ℝ (e 0) (c k - c i) • e 0 + inner ℝ (e 1) (c k - c i) • e 1)
    (ha : 0 < q c i j) (hd : dist (c i) (c j) < 2)
    (hQ : 0 < Qf c i j k) (t : ℝ) :
    SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.sphere (c k) 1 ↔
      ∃ n : ℤ, t =
        Complex.arg ⟨inner ℝ (e 0) (c k - c i), inner ℝ (e 1) (c k - c i)⟩ +
          betaA c i j k + 2 * Real.pi * n ∨ t =
        Complex.arg ⟨inner ℝ (e 0) (c k - c i), inner ℝ (e 1) (c k - c i)⟩ -
          betaA c i j k + 2 * Real.pi * n := by
  have ha4 : q c i j < 4 := by unfold q; nlinarith [dist_nonneg (x := c i) (y := c j)]
  rcases p3_beta_cos_ratio c i j k ha ha4 hQ with ⟨hp, hβ⟩
  have hpn := p3_projection_phase_norm c i j k e he hframe
  have hz : (⟨inner ℝ (e 0) (c k - c i), inner ℝ (e 1) (c k - c i)⟩ : ℂ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hpn]
    exact ne_of_gt hp
  have hcoeff := CircleArc.phase_cos (inner ℝ (e 0) (c k - c i))
    (inner ℝ (e 1) (c k - c i)) t hz
  rw [hpn] at hcoeff
  have hR : 0 < 4 * Real.sqrt (1 - q c i j / 4) *
      ‖perpProj (c j - c i) (c k - c i)‖ := by
    apply mul_pos _ hp
    apply mul_pos (by norm_num)
    apply Real.sqrt_pos.mpr
    linarith
  rw [p3_pair_circle_sphere_cut c i j k e he hperp hd t]
  rw [← CircleArc.cos_endpoint_periodic_shift (betaA c i j k) _ t]
  rw [hβ, eq_div_iff (ne_of_gt hR)]
  have hcoeff' := congrArg (fun r : ℝ => 4 * Real.sqrt (1 - q c i j / 4) * r) hcoeff
  constructor <;> intro h <;> nlinarith [hcoeff']

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_cut_cos (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (θ : ℝ)
    (haligned : perpProj (c j - c i) (c k - c i) =
      ‖perpProj (c j - c i) (c k - c i)‖ •
        (Real.cos θ • e 0 + Real.sin θ • e 1))
    (ha : 0 < q c i j) (hd : dist (c i) (c j) < 2)
    (hQ : 0 < Qf c i j k) (t : ℝ) :
    (SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.closedBall (c k) 1 ↔
        Real.cos (betaA c i j k) ≤ Real.cos (t - θ)) ∧
    (SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.sphere (c k) 1 ↔
        Real.cos (betaA c i j k) = Real.cos (t - θ)) := by
  have he00 : inner ℝ (e 0) (e 0) = 1 := by simpa using (orthonormal_iff_ite.mp he) 0 0
  have he01 : inner ℝ (e 0) (e 1) = 0 := by simpa using (orthonormal_iff_ite.mp he) 0 1
  have he10 : inner ℝ (e 1) (e 0) = 0 := by simpa using (orthonormal_iff_ite.mp he) 1 0
  have he11 : inner ℝ (e 1) (e 1) = 1 := by simpa using (orthonormal_iff_ite.mp he) 1 1
  have he0v : inner ℝ (e 0) (c j - c i) = 0 := by rw [real_inner_comm]; exact hperp 0
  have he1v : inner ℝ (e 1) (c j - c i) = 0 := by rw [real_inner_comm]; exact hperp 1
  have h0 : inner ℝ (e 0) (c k - c i) =
      ‖perpProj (c j - c i) (c k - c i)‖ * Real.cos θ := by
    calc
      _ = inner ℝ (e 0) (perpProj (c j - c i) (c k - c i)) := by
        unfold perpProj
        conv_rhs => rw [inner_sub_right, real_inner_smul_right, he0v]
        ring
      _ = _ := by
        conv_lhs => rw [haligned]
        simp only [inner_add_right, real_inner_smul_right, he00, he01]
        ring
  have h1 : inner ℝ (e 1) (c k - c i) =
      ‖perpProj (c j - c i) (c k - c i)‖ * Real.sin θ := by
    calc
      _ = inner ℝ (e 1) (perpProj (c j - c i) (c k - c i)) := by
        unfold perpProj
        conv_rhs => rw [inner_sub_right, real_inner_smul_right, he1v]
        ring
      _ = _ := by
        conv_lhs => rw [haligned]
        simp only [inner_add_right, real_inner_smul_right, he10, he11]
        ring
  have hcoeff : Real.cos t * inner ℝ (e 0) (c k - c i) +
      Real.sin t * inner ℝ (e 1) (c k - c i) =
      ‖perpProj (c j - c i) (c k - c i)‖ * Real.cos (t - θ) := by
    rw [h0, h1, Real.cos_sub]
    ring
  have ha4 : q c i j < 4 := by unfold q; nlinarith [dist_nonneg (x := c i) (y := c j)]
  rcases p3_beta_cos_ratio c i j k ha ha4 hQ with ⟨hp, hβ⟩
  have hR : 0 < 4 * Real.sqrt (1 - q c i j / 4) *
      ‖perpProj (c j - c i) (c k - c i)‖ := by
    apply mul_pos _ hp
    apply mul_pos (by norm_num)
    apply Real.sqrt_pos.mpr
    linarith
  constructor
  · rw [p3_pair_circle_ball_cut c i j k e he hperp hd t, hcoeff, hβ, div_le_iff₀ hR]
    congr 1
    ring
  · rw [p3_pair_circle_sphere_cut c i j k e he hperp hd t, hcoeff, hβ,
      div_eq_iff (ne_of_gt hR)]
    congr 1
    ring

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_ball_beta_aligned (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (θ : ℝ)
    (haligned : perpProj (c j - c i) (c k - c i) =
      ‖perpProj (c j - c i) (c k - c i)‖ •
        (Real.cos θ • e 0 + Real.sin θ • e 1))
    (ha : 0 < q c i j) (hd : dist (c i) (c j) < 2)
    (hQ : 0 < Qf c i j k) (t : ℝ) :
    SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.closedBall (c k) 1 ↔
        ∃ n : ℤ, t ∈ Set.Icc (θ - betaA c i j k + 2 * Real.pi * n)
          (θ + betaA c i j k + 2 * Real.pi * n) := by
  exact (p3_pair_circle_cut_cos c i j k e he hperp θ haligned ha hd hQ t).1.trans
    (CircleArc.cos_cut_periodic_shift (betaA c i j k) θ t
      (p3_betaA_range c i j k hQ).1.le (p3_betaA_range c i j k hQ).2.le)

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_sphere_beta_aligned (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (θ : ℝ)
    (haligned : perpProj (c j - c i) (c k - c i) =
      ‖perpProj (c j - c i) (c k - c i)‖ •
        (Real.cos θ • e 0 + Real.sin θ • e 1))
    (ha : 0 < q c i j) (hd : dist (c i) (c j) < 2)
    (hQ : 0 < Qf c i j k) (t : ℝ) :
    SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) t ∈ Metric.sphere (c k) 1 ↔
        ∃ n : ℤ, t = θ + betaA c i j k + 2 * Real.pi * n ∨
          t = θ - betaA c i j k + 2 * Real.pi * n := by
  rw [(p3_pair_circle_cut_cos c i j k e he hperp θ haligned ha hd hQ t).2, eq_comm]
  exact CircleArc.cos_endpoint_periodic_shift (betaA c i j k) θ t

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_pair_circle_ball_beta_preimage (c : Fin 4 → Pt) (i j k : Fin 4)
    (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hperp : ∀ n, inner ℝ (c j - c i) (e n) = 0)
    (θ : ℝ)
    (haligned : perpProj (c j - c i) (c k - c i) =
      ‖perpProj (c j - c i) (c k - c i)‖ •
        (Real.cos θ • e 0 + Real.sin θ • e 1))
    (ha : 0 < q c i j) (hd : dist (c i) (c j) < 2)
    (hQ : 0 < Qf c i j k) :
    SphereGeom.circlePt ((1 / 2 : ℝ) • (c i + c j)) (e 0) (e 1)
      (Real.sqrt (1 - q c i j / 4)) ⁻¹' Metric.closedBall (c k) 1 =
      ⋃ n : ℤ, Set.Icc (θ - betaA c i j k + 2 * Real.pi * n)
        (θ + betaA c i j k + 2 * Real.pi * n) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_iUnion]
  exact p3_pair_circle_ball_beta_aligned c i j k e he hperp θ haligned ha hd hQ t

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_circle_point_int_periodic (m u v : Pt) (r t : ℝ) (n : ℤ) :
    SphereGeom.circlePt m u v r (t + 2 * Real.pi * n) =
      SphereGeom.circlePt m u v r t := by
  rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring]
  simp only [SphereGeom.circlePt, Real.cos_add_int_mul_two_pi,
    Real.sin_add_int_mul_two_pi]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_circle_cos_cut_image (m u v : Pt) (r β θ : ℝ)
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    SphereGeom.circlePt m u v r '' {t | Real.cos β ≤ Real.cos (t - θ)} =
      SphereGeom.circlePt m u v r '' Set.Icc (θ - β) (θ + β) := by
  ext x
  constructor
  · rintro ⟨t, hcos, ht⟩
    obtain ⟨n, hn0, hn1⟩ := (CircleArc.cos_cut_periodic_shift β θ t hβ0 hβπ).mp hcos
    refine ⟨t - 2 * Real.pi * n, ⟨by linarith, by linarith⟩, ?_⟩
    calc
      _ = SphereGeom.circlePt m u v r t := by
        rw [show t - 2 * Real.pi * n = t + 2 * Real.pi * (-n) by simp; ring]
        simpa only [Int.cast_neg] using p3_circle_point_int_periodic m u v r t (-n)
      _ = x := ht
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ?_, htx⟩
    exact (CircleArc.cos_cut_periodic_shift β θ t hβ0 hβπ).mpr
      ⟨0, by simpa only [Int.cast_zero, mul_zero, add_zero] using ht⟩

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_circle_cos_endpoint_image (m u v : Pt) (r β θ : ℝ) :
    SphereGeom.circlePt m u v r '' {t | Real.cos (t - θ) = Real.cos β} =
      {SphereGeom.circlePt m u v r (θ - β),
        SphereGeom.circlePt m u v r (θ + β)} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht, htx⟩
    obtain ⟨n, hp | hm⟩ := (CircleArc.cos_endpoint_periodic_shift β θ t).mp ht
    · right
      rw [hp, p3_circle_point_int_periodic] at htx
      exact htx.symm
    · left
      rw [hm, p3_circle_point_int_periodic] at htx
      exact htx.symm
  · intro h
    rcases h with rfl | rfl
    · exact ⟨θ - β, by rw [sub_sub_cancel_left, Real.cos_neg], rfl⟩
    · exact ⟨θ + β, by rw [add_sub_cancel_left], rfl⟩

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)

private structure HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel (c : Fin 4 → Pt) (i j : Fin 4) where
  e : Fin 2 → Pt
  ortho : Orthonormal ℝ e
  perp : ∀ n, inner ℝ (c j - c i) (e n) = 0
  dist_pos : 0 < dist (c i) (c j)
  dist_lt_two : dist (c i) (c j) < 2
  betaA_range : 0 < betaA c i j (oth1 i j) ∧ betaA c i j (oth1 i j) < Real.pi
  betaB_range : 0 < betaA c i j (oth2 i j) ∧ betaA c i j (oth2 i j) < Real.pi
  phi_range : 0 < phiE c i j ∧ phiE c i j < Real.pi
  ballA : ∀ t, SphereGeom.circlePt ((1/2:ℝ) • (c i+c j)) (e 0) (e 1)
    (Real.sqrt (1-q c i j/4)) t ∈ Metric.closedBall (c (oth1 i j)) 1 ↔
      Real.cos (betaA c i j (oth1 i j)) ≤ Real.cos t
  ballB : ∀ t, SphereGeom.circlePt ((1/2:ℝ) • (c i+c j)) (e 0) (e 1)
    (Real.sqrt (1-q c i j/4)) t ∈ Metric.closedBall (c (oth2 i j)) 1 ↔
      Real.cos (betaA c i j (oth2 i j)) ≤ Real.cos (t-phiE c i j)
  sphereA : ∀ t, SphereGeom.circlePt ((1/2:ℝ) • (c i+c j)) (e 0) (e 1)
    (Real.sqrt (1-q c i j/4)) t ∈ Metric.sphere (c (oth1 i j)) 1 ↔
      Real.cos t = Real.cos (betaA c i j (oth1 i j))
  sphereB : ∀ t, SphereGeom.circlePt ((1/2:ℝ) • (c i+c j)) (e 0) (e 1)
    (Real.sqrt (1-q c i j/4)) t ∈ Metric.sphere (c (oth2 i j)) 1 ↔
      Real.cos (t-phiE c i j) = Real.cos (betaA c i j (oth2 i j))

private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.point {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : ℝ → Pt :=
  SphereGeom.circlePt ((1/2:ℝ) • (c i+c j)) (M.e 0) (M.e 1) (Real.sqrt (1-q c i j/4))
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.arcA {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : Set Pt :=
  M.point '' Set.Icc (-betaA c i j (oth1 i j)) (betaA c i j (oth1 i j))
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.arcB {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : Set Pt :=
  M.point '' Set.Icc (phiE c i j-betaA c i j (oth2 i j)) (phiE c i j+betaA c i j (oth2 i j))

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_exists_cos_model (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    Nonempty (P3PairCosModel c i j) := by
  obtain ⟨e, he, hp, hu, hv⟩ := p3_pair_aligned_frame hc i j hij
  have hq := p3_q_pos_lt_four hc i j hij
  have hd0 : 0 < dist (c i) (c j) := by
    have hn := dist_nonneg (x := c i) (y := c j)
    have h0 := hq.1
    unfold q at h0
    nlinarith
  have hd2 : dist (c i) (c j) < 2 := by
    have hn := dist_nonneg (x := c i) (y := c j)
    have h4 := hq.2
    unfold q at h4
    nlinarith
  have hQ := p3_pair_Q_pos hc i j hij
  have hA := p3_betaA_range c i j (oth1 i j) hQ.1
  have hB := p3_betaA_range c i j (oth2 i j) hQ.2
  have hu' : perpProj (c j - c i) (c (oth1 i j) - c i) =
      ‖perpProj (c j - c i) (c (oth1 i j) - c i)‖ •
        (Real.cos (0 : ℝ) • e 0 + Real.sin (0 : ℝ) • e 1) := by
    simpa only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] using hu
  refine ⟨⟨e, he, hp, hd0, hd2, hA, hB, p3_phi_range hc i j hij, ?_, ?_, ?_, ?_⟩⟩
  · intro t
    simpa only [sub_zero] using
      (p3_pair_circle_cut_cos c i j (oth1 i j) e he hp 0 hu' hq.1 hd2 hQ.1 t).1
  · intro t
    exact (p3_pair_circle_cut_cos c i j (oth2 i j) e he hp _ hv hq.1 hd2 hQ.2 t).1
  · intro t
    simpa only [sub_zero] using
      ((p3_pair_circle_cut_cos c i j (oth1 i j) e he hp 0 hu' hq.1 hd2 hQ.1 t).2.trans eq_comm)
  · intro t
    exact (p3_pair_circle_cut_cos c i j (oth2 i j) e he hp _ hv hq.1 hd2 hQ.2 t).2.trans eq_comm

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_spheres (c : Fin 4 → Pt) (i j : Fin 4) (M : P3PairCosModel c i j) :
    Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 = M.point '' Set.Icc 0 (2*Real.pi) := by
  exact CircleArc.pair_sphere_chart_two (c i) (c j) M.e M.ortho M.perp M.dist_pos M.dist_lt_two

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_point_on_spheres (c : Fin 4 → Pt) (i j : Fin 4)
    (M : P3PairCosModel c i j) (t : ℝ) :
    M.point t ∈ Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 := by
  exact CircleArc.pair_circle_on_spheres (c i) (c j) M.e M.ortho M.perp M.dist_lt_two t

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_ballA_set (c : Fin 4 → Pt) (i j : Fin 4) (M : P3PairCosModel c i j) :
    Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 ∩
      Metric.closedBall (c (oth1 i j)) 1 = M.arcA := by
  have hcos := p3_circle_cos_cut_image ((1/2:ℝ) • (c i+c j)) (M.e 0) (M.e 1)
    (Real.sqrt (1-q c i j/4)) (betaA c i j (oth1 i j)) 0
      M.betaA_range.1.le M.betaA_range.2.le
  simp only [zero_sub, zero_add, sub_zero] at hcos
  change M.point '' _ = M.arcA at hcos
  rw [← hcos]
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    rw [p3_model_spheres c i j M] at hx
    obtain ⟨t, ht, htx⟩ := hx
    refine ⟨t, (M.ballA t).mp ?_, htx⟩
    rw [← htx] at hb
    exact hb
  · rintro ⟨t, ht, rfl⟩
    exact ⟨p3_model_point_on_spheres c i j M t, (M.ballA t).mpr ht⟩

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_ballB_set (c : Fin 4 → Pt) (i j : Fin 4) (M : P3PairCosModel c i j) :
    Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 ∩
      Metric.closedBall (c (oth2 i j)) 1 = M.arcB := by
  have hcos := p3_circle_cos_cut_image ((1/2:ℝ) • (c i+c j)) (M.e 0) (M.e 1)
    (Real.sqrt (1-q c i j/4)) (betaA c i j (oth2 i j)) (phiE c i j)
      M.betaB_range.1.le M.betaB_range.2.le
  change M.point '' _ = M.arcB at hcos
  rw [← hcos]
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    rw [p3_model_spheres c i j M] at hx
    obtain ⟨t, ht, htx⟩ := hx
    refine ⟨t, (M.ballB t).mp ?_, htx⟩
    rw [← htx] at hb
    exact hb
  · rintro ⟨t, ht, rfl⟩
    exact ⟨p3_model_point_on_spheres c i j M t, (M.ballB t).mpr ht⟩

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_locus (c : Fin 4 → Pt) (i j : Fin 4) (hij : i ≠ j)
    (M : P3PairCosModel c i j) :
    Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 ∩ Kset c = M.arcA ∩ M.arcB := by
  rw [p3_pair_locus_eq c i j hij, ← p3_model_ballA_set c i j M, ← p3_model_ballB_set c i j M]
  ext x
  simp only [Set.mem_inter_iff]
  tauto

open MeasureTheory SphereGeom
noncomputable section

open CircleArc

private theorem CircleArc.periodicPointEq (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e)
    (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (u v : ℝ) (hu : u ∈ Set.Icc (-a) a)
    (hv : v ∈ Set.Icc (φ - b) (φ + b)) :
    circlePt c (e 0) (e 1) r u = circlePt c (e 0) (e 1) r v ↔
      u = v ∨ u = v - 2 * Real.pi := by
  constructor
  · intro heq
    have h0 := congrArg (fun p : E3 => inner ℝ (e 0) p) heq
    have h1 := congrArg (fun p : E3 => inner ℝ (e 1) p) heq
    have he00 : inner ℝ (e 0) (e 0) = 1 := by
      simpa using (orthonormal_iff_ite.mp he) 0 0
    have he01 : inner ℝ (e 0) (e 1) = 0 := by
      simpa using (orthonormal_iff_ite.mp he) 0 1
    have he10 : inner ℝ (e 1) (e 0) = 0 := by
      simpa using (orthonormal_iff_ite.mp he) 1 0
    have he11 : inner ℝ (e 1) (e 1) = 1 := by
      simpa using (orthonormal_iff_ite.mp he) 1 1
    simp only [circlePt, inner_add_right, inner_smul_right,
      he00, he01, he10, he11, mul_one, mul_zero, add_zero, zero_add] at h0 h1
    have hc : Real.cos u = Real.cos v :=
      mul_left_cancel₀ (ne_of_gt hr) (add_left_cancel h0)
    have hs : Real.sin u = Real.sin v :=
      mul_left_cancel₀ (ne_of_gt hr) (add_left_cancel h1)
    have hcos : Real.cos (u - v) = 1 := by
      rw [Real.cos_sub, hc, hs]
      nlinarith [Real.sin_sq_add_cos_sq v]
    have hlo : -(4 * Real.pi) < u - v := by
      linarith [hu.1, hv.2, Real.pi_pos]
    have hhi : u - v < 2 * Real.pi := by
      linarith [hu.2, hv.1]
    by_cases hcentral : -(2 * Real.pi) < u - v
    · left
      have hz := (Real.cos_eq_one_iff_of_lt_of_lt hcentral hhi).mp hcos
      linarith
    · right
      have hshift : Real.cos (u - v + 2 * Real.pi) = 1 := by
        simpa only [Real.cos_add_two_pi] using hcos
      have hz := (Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith) (by linarith [Real.pi_pos])).mp hshift
      linarith
  · rintro (h | h)
    · rw [h]
    · rw [h]
      simp only [circlePt, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

private theorem CircleArc.periodicMembership (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e)
    (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (t : ℝ) (ht : t ∈ Set.Icc (-a) a) :
    circlePt c (e 0) (e 1) r t ∈
        circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b) ↔
      (φ - b ≤ t ∧ t ≤ φ + b) ∨ t ≤ φ + b - 2 * Real.pi := by
  constructor
  · rintro ⟨v, hv, heq⟩
    rcases (periodicPointEq c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ
      t v ht hv).mp heq.symm with h | h
    · left
      simpa only [Set.mem_Icc, h] using hv
    · right
      linarith [hv.2]
  · rintro (h | h)
    · exact ⟨t, h, rfl⟩
    · refine ⟨t + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
      · linarith [ht.1]
      · linarith
      · simp only [circlePt, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem CircleArc.periodicIntersection (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e)
    (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    (circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) =
      (circlePt c (e 0) (e 1) r ''
        Set.Icc (max (-a) (φ - b)) (min a (φ + b))) ∪
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) (φ + b - 2 * Real.pi)) ∧
    Disjoint
      (circlePt c (e 0) (e 1) r '' Set.Icc (max (-a) (φ - b)) (min a (φ + b)))
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) (φ + b - 2 * Real.pi)) ∧
    arcMeasure (circlePt c (e 0) (e 1) r ''
        Set.Icc (max (-a) (φ - b)) (min a (φ + b))) =
      ENNReal.ofReal (r * (min a (φ + b) - max (-a) (φ - b))) ∧
    arcMeasure (circlePt c (e 0) (e 1) r '' Set.Icc (-a) (φ + b - 2 * Real.pi)) =
      ENNReal.ofReal (r * (a + b + φ - 2 * Real.pi)) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
      ENNReal.ofReal (r * (min a (φ + b) - max (-a) (φ - b))) +
      ENNReal.ofReal (r * (a + b + φ - 2 * Real.pi)) := by
  let F : ℝ → E3 := circlePt c (e 0) (e 1) r
  let L := max (-a) (φ - b)
  let U := min a (φ + b)
  let V := φ + b - 2 * Real.pi
  have hLa : -a ≤ L := le_max_left _ _
  have hLb : φ - b ≤ L := le_max_right _ _
  have hUa : U ≤ a := min_le_left _ _
  have hUb : U ≤ φ + b := min_le_right _ _
  have hVa : V ≤ a := by dsimp [V]; linarith
  have hgap : V < L := by
    apply lt_of_lt_of_le _ hLb
    dsimp [V]
    linarith
  have hsets : (F '' Set.Icc (-a) a) ∩ (F '' Set.Icc (φ - b) (φ + b)) =
      (F '' Set.Icc L U) ∪ (F '' Set.Icc (-a) V) := by
    ext p
    constructor
    · rintro ⟨⟨t, ht, htp⟩, hpB⟩
      have hmem : F t ∈ F '' Set.Icc (φ - b) (φ + b) := by
        rw [htp]
        exact hpB
      rcases (periodicMembership c e he r hr a b φ ha0 haπ hb0 hbπ
        hφ0 hφπ t ht).mp hmem with h | h
      · left
        refine ⟨t, ⟨?_, ?_⟩, htp⟩
        · exact max_le ht.1 h.1
        · exact le_min ht.2 h.2
      · right
        exact ⟨t, ⟨ht.1, h⟩, htp⟩
    · rintro (⟨t, ht, htp⟩ | ⟨t, ht, htp⟩)
      · have htA : t ∈ Set.Icc (-a) a :=
          ⟨le_trans hLa ht.1, le_trans ht.2 hUa⟩
        have htB : t ∈ Set.Icc (φ - b) (φ + b) :=
          ⟨le_trans hLb ht.1, le_trans ht.2 hUb⟩
        exact ⟨⟨t, htA, htp⟩, ⟨t, htB, htp⟩⟩
      · have htA : t ∈ Set.Icc (-a) a :=
          ⟨ht.1, le_trans ht.2 hVa⟩
        refine ⟨⟨t, htA, htp⟩, ?_⟩
        rw [← htp]
        exact (periodicMembership c e he r hr a b φ ha0 haπ hb0 hbπ
          hφ0 hφπ t htA).mpr (Or.inr ht.2)
  have hd : Disjoint (F '' Set.Icc L U) (F '' Set.Icc (-a) V) := by
    have hspan : max U V - min L (-a) < 2 * Real.pi := by
      rw [min_eq_right hLa]
      have hm : max U V ≤ a := max_le hUa hVa
      linarith
    have hi := (intervalIntersection c e he r hr L U (-a) V hspan).1
    have hempty : Set.Icc (max L (-a)) (min U V) = ∅ :=
      Set.Icc_eq_empty_of_lt
        (lt_of_le_of_lt (min_le_right U V)
          (lt_of_lt_of_le hgap (le_max_left L (-a))))
    apply Set.disjoint_iff_inter_eq_empty.mpr
    simpa only [hempty, Set.image_empty] using hi
  have hmC : arcMeasure (F '' Set.Icc L U) = ENNReal.ofReal (r * (U - L)) := by
    have hspan : max U U - min L L < 2 * Real.pi := by
      simp only [max_self, min_self]
      linarith
    simpa only [Set.inter_self, max_self, min_self] using
      (intervalIntersection c e he r hr L U L U hspan).2
  have hmW : arcMeasure (F '' Set.Icc (-a) V) =
      ENNReal.ofReal (r * (a + b + φ - 2 * Real.pi)) := by
    have hspan : max V V - min (-a) (-a) < 2 * Real.pi := by
      simp only [max_self, min_self]
      dsimp [V]
      linarith [Real.pi_pos]
    have hm := (intervalIntersection c e he r hr (-a) V (-a) V hspan).2
    simp only [Set.inter_self, max_self, min_self] at hm
    calc
      arcMeasure (F '' Set.Icc (-a) V) = ENNReal.ofReal (r * (V - (-a))) := hm
      _ = ENNReal.ofReal (r * (a + b + φ - 2 * Real.pi)) := by
        dsimp [V]
        congr 1
        ring
  have hcont : Continuous F := by
    change Continuous (fun t : ℝ => c + r • (Real.cos t • e 0 + Real.sin t • e 1))
    fun_prop
  have hmeas : MeasurableSet (F '' Set.Icc (-a) V) :=
    (isCompact_Icc.image hcont).isClosed.measurableSet
  refine ⟨hsets, hd, hmC, hmW, ?_⟩
  rw [hsets, measure_union hd hmeas, hmC, hmW]

private theorem CircleArc.periodicIntersectionCommon (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hwrap : 2 * Real.pi ≤ a + b + φ) :
    (circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) =
      (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) a) ∪
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) (φ + b - 2 * Real.pi)) ∧
    Disjoint (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) a)
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) (φ + b - 2 * Real.pi)) ∧
    φ - b < a ∧ -a ≤ φ + b - 2 * Real.pi ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
      ENNReal.ofReal (r * (2 * a + 2 * b - 2 * Real.pi)) := by
  have hlow : -a ≤ φ - b := by linarith
  have hup : a ≤ φ + b := by linarith
  have hmeet : φ - b < a := by linarith
  have hW : -a ≤ φ + b - 2 * Real.pi := by linarith
  have h := periodicIntersection c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ
  simp only [max_eq_right hlow, min_eq_left hup] at h
  refine ⟨h.1, h.2.1, hmeet, hW, ?_⟩
  rw [h.2.2.2.2]
  have hC0 : 0 ≤ r * (a - (φ - b)) :=
    mul_nonneg (le_of_lt hr) (by linarith)
  have hW0 : 0 ≤ r * (a + b + φ - 2 * Real.pi) :=
    mul_nonneg (le_of_lt hr) (by linarith)
  rw [← ENNReal.ofReal_add hC0 hW0]
  congr 1
  ring

private def CircleArc.EndpointWidth.countTwo (p q : Prop) : ℕ := by
  classical
  exact (if p then 1 else 0) + (if q then 1 else 0)

open CircleArc.EndpointWidth
private theorem CircleArc.EndpointWidth.countTwo_zero (p q : Prop) : countTwo p q = 0 ↔ ¬p ∧ ¬q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [countTwo, hp, hq]

private theorem CircleArc.EndpointWidth.countTwo_one (p q : Prop) :
    countTwo p q = 1 ↔ (p ∧ ¬q) ∨ (¬p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [countTwo, hp, hq]

private theorem CircleArc.EndpointWidth.countTwo_two (p q : Prop) : countTwo p q = 2 ↔ p ∧ q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [countTwo, hp, hq]

private def CircleArc.EndpointWidth.countA (a b φ : ℝ) : ℕ :=
  countTwo (φ + a ≤ b ∨ 2 * Real.pi ≤ a + b + φ)
    (φ - b ≤ a ∧ a ≤ φ + b)

private def CircleArc.EndpointWidth.countB (a b φ : ℝ) : ℕ :=
  countTwo (-a ≤ φ - b ∧ φ - b ≤ a)
    (φ + b ≤ a ∨ 2 * Real.pi ≤ a + b + φ)

private theorem CircleArc.EndpointWidth.wrap_inequalities (a b φ : ℝ) (ha : a < Real.pi) (hb : b < Real.pi)
    (hφ : φ < Real.pi) (hw : 2 * Real.pi ≤ a + b + φ) :
    |a - b| < φ ∧ φ < a + b := by
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  · linarith

private theorem CircleArc.EndpointWidth.bulk_of_counts (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 1) (hB : countB a b φ = 1) :
    |a - b| < φ ∧ φ ≤ a + b ∧ a + b + φ < 2 * Real.pi := by
  have hwrap : a + b + φ < 2 * Real.pi := by
    by_contra hn
    have hw : 2 * Real.pi ≤ a + b + φ := le_of_not_gt hn
    have hv := wrap_inequalities a b φ haπ hbπ hφπ hw
    have haFlag : φ - b ≤ a ∧ a ≤ φ + b := by
      rcases abs_lt.mp hv.1 with ⟨hl, hu⟩
      constructor <;> linarith [hv.2]
    have htwo : countA a b φ = 2 :=
      (countTwo_two _ _).mpr ⟨Or.inr hw, haFlag⟩
    omega
  rcases (countTwo_one _ _).mp hA with hA | hA
  · rcases hA.1 with hcont | hw
    · rcases (countTwo_one _ _).mp hB with hB | hB
      · rcases hB.1 with ⟨hl, hu⟩
        exfalso
        apply hA.2
        constructor <;> linarith
      · rcases hB.2 with hcontB | hw
        · linarith
        · linarith
    · linarith
  · have hnotA : ¬φ + a ≤ b := fun h => hA.1 (Or.inl h)
    have hrightA := hA.2
    rcases (countTwo_one _ _).mp hB with hB | hB
    · have hnotB : ¬φ + b ≤ a := fun h => hB.2 (Or.inl h)
      have hleftB := hB.1
      refine ⟨?_, ?_, hwrap⟩
      · rw [abs_lt]
        constructor <;> linarith
      · linarith [hrightA.1]
    · rcases hB.2 with hcontB | hw
      · exfalso
        apply hB.1
        constructor <;> linarith
      · linarith

private theorem CircleArc.EndpointWidth.containsA_of_counts (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 2) (hB : countB a b φ = 0) : φ + a < b := by
  have hA' := (countTwo_two _ _).mp hA
  have hB' := (countTwo_zero _ _).mp hB
  rcases hA'.1 with hcont | hw
  · by_contra hn
    have hge : b ≤ φ + a := le_of_not_gt hn
    apply hB'.1
    constructor <;> linarith [hA'.2.1]
  · exact False.elim (hB'.2 (Or.inr hw))

private theorem CircleArc.EndpointWidth.containsB_of_counts (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 0) (hB : countB a b φ = 2) : φ + b < a := by
  have hA' := (countTwo_zero _ _).mp hA
  have hB' := (countTwo_two _ _).mp hB
  rcases hB'.2 with hcont | hw
  · by_contra hn
    have hge : a ≤ φ + b := le_of_not_gt hn
    apply hA'.2
    constructor <;> linarith [hB'.1.2]
  · exact False.elim (hA'.1 (Or.inr hw))

private theorem CircleArc.EndpointWidth.empty_of_counts (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 0) (hB : countB a b φ = 0) : a + b < φ := by
  have hA' := (countTwo_zero _ _).mp hA
  have hB' := (countTwo_zero _ _).mp hB
  by_contra hn
  have hmeet : φ ≤ a + b := le_of_not_gt hn
  have hab : a ≤ φ + b := by
    by_contra hh
    have hh' : φ + b < a := lt_of_not_ge hh
    apply hB'.2
    exact Or.inl (le_of_lt hh')
  exact hA'.2 ⟨by linarith, hab⟩

private theorem CircleArc.EndpointWidth.common_of_counts (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 2) (hB : countB a b φ = 2) :
    2 * Real.pi ≤ a + b + φ := by
  have hA' := (countTwo_two _ _).mp hA
  have hB' := (countTwo_two _ _).mp hB
  rcases hA'.1 with hcontA | hw
  · rcases hB'.2 with hcontB | hw
    · linarith
    · exact hw
  · exact hw

private theorem CircleArc.EndpointWidth.proper_excludes_antipode (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi) :
    circlePt c (e 0) (e 1) r Real.pi ∉
      circlePt c (e 0) (e 1) r '' Set.Icc (-a) a := by
  have hlow : -a ≤ Real.pi := by linarith [Real.pi_pos]
  have hhigh : a ≤ Real.pi := le_of_lt haπ
  have h := CircleArc.intervalIntersection c e he r hr (-a) a Real.pi Real.pi
    (by rw [max_eq_right hhigh, min_eq_left hlow]; linarith)
  have he0 : Set.Icc Real.pi a = ∅ := Set.Icc_eq_empty_of_lt haπ
  have hsets : (circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
      (circlePt c (e 0) (e 1) r '' Set.Icc Real.pi Real.pi) = ∅ := by
    simpa only [max_eq_right hlow, min_eq_left hhigh, he0, Set.image_empty] using h.1
  intro hmem
  have hp : circlePt c (e 0) (e 1) r Real.pi ∈
      circlePt c (e 0) (e 1) r '' Set.Icc Real.pi Real.pi :=
    ⟨Real.pi, ⟨le_rfl, le_rfl⟩, rfl⟩
  have hi : circlePt c (e 0) (e 1) r Real.pi ∈
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
      (circlePt c (e 0) (e 1) r '' Set.Icc Real.pi Real.pi) := ⟨hmem, hp⟩
  rw [hsets] at hi
  exact hi

private theorem CircleArc.EndpointWidth.intersection_ne_full_circle (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi) (B : Set E3) :
    (circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩ B ≠
      Set.range (circlePt c (e 0) (e 1) r) := by
  intro h
  have hp : circlePt c (e 0) (e 1) r Real.pi ∈
      Set.range (circlePt c (e 0) (e 1) r) := ⟨Real.pi, rfl⟩
  rw [← h] at hp
  exact proper_excludes_antipode c e he r hr a ha0 haπ hp.1

private theorem CircleArc.EndpointWidth.bulk_measure_of_counts (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 1) (hB : countB a b φ = 1) :
    ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) =
      circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) a) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
      ENNReal.ofReal (r * (a + b - φ)) := by
  obtain ⟨hdiff, hmeet, hspan0⟩ := bulk_of_counts a b φ ha0 haπ hb0 hbπ hφ0 hφπ hA hB
  rcases abs_lt.mp hdiff with ⟨hdiffL, hdiffR⟩
  have hl : -a ≤ φ - b := by linarith
  have hu : a ≤ φ + b := by linarith
  have hspan : max a (φ + b) - min (-a) (φ - b) < 2 * Real.pi := by
    rw [max_eq_right hu, min_eq_left hl]
    linarith
  have h := CircleArc.intervalIntersection c e he r hr (-a) a (φ - b) (φ + b) hspan
  simp only [max_eq_right hl, min_eq_left hu] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  congr 1
  ring

private theorem CircleArc.EndpointWidth.containsA_measure_of_counts (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 2) (hB : countB a b φ = 0) :
    ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) =
      circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
      ENNReal.ofReal (2 * r * a) := by
  have hcont := containsA_of_counts a b φ ha0 haπ hb0 hbπ hφ0 hφπ hA hB
  have hsub : Set.Icc (-a) a ⊆ Set.Icc (φ - b) (φ + b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsets : (circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
      (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) =
      circlePt c (e 0) (e 1) r '' Set.Icc (-a) a :=
    Set.inter_eq_left.mpr (Set.image_mono hsub)
  have hmeasure := SphereGeom.arcMeasure_circle_arc c e he r hr (-a) a
    (by linarith) (by linarith)
  refine ⟨hsets, ?_⟩
  rw [hsets, hmeasure]
  congr 1
  ring

private theorem CircleArc.EndpointWidth.containsB_measure_of_counts (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 0) (hB : countB a b φ = 2) :
    ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) =
      circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
      ENNReal.ofReal (2 * r * b) := by
  have hcont := containsB_of_counts a b φ ha0 haπ hb0 hbπ hφ0 hφπ hA hB
  exact (CircleArc.arcIntersectionCases c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ).2.1
    (le_of_lt hcont)

private theorem CircleArc.EndpointWidth.empty_measure_of_counts (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 0) (hB : countB a b φ = 0) :
    ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) = ∅) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) = 0 := by
  have hsep := empty_of_counts a b φ ha0 haπ hb0 hbπ hφ0 hφπ hA hB
  exact (CircleArc.arcIntersectionCases c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ).2.2 hsep

private theorem CircleArc.EndpointWidth.point_mem_arc_iff_of_span (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (t l u : ℝ)
    (hspan : max t u - min t l < 2 * Real.pi) :
    circlePt c (e 0) (e 1) r t ∈ circlePt c (e 0) (e 1) r '' Set.Icc l u ↔
      l ≤ t ∧ t ≤ u := by
  constructor
  · intro hm
    have hs : circlePt c (e 0) (e 1) r t ∈
        circlePt c (e 0) (e 1) r '' Set.Icc t t := ⟨t, ⟨le_rfl, le_rfl⟩, rfl⟩
    have hi : circlePt c (e 0) (e 1) r t ∈
        (circlePt c (e 0) (e 1) r '' Set.Icc t t) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc l u) := ⟨hs, hm⟩
    rw [(CircleArc.intervalIntersection c e he r hr t t l u hspan).1] at hi
    rcases hi with ⟨v, hv, _⟩
    constructor
    · exact le_trans (le_max_right _ _) (le_trans hv.1 (le_trans hv.2 (min_le_left _ _)))
    · exact le_trans (le_max_left _ _) (le_trans hv.1 (le_trans hv.2 (min_le_right _ _)))
  · intro ht
    exact ⟨t, ht, rfl⟩

private theorem CircleArc.EndpointWidth.span_of_bounds (t l u M : ℝ) (hM : 0 < M)
    (hleft : t - l < M) (hright : u - t < M) (hlen : u - l < M) :
    max t u - min t l < M := by
  rw [max_def, min_def]
  split_ifs <;> linarith

private theorem CircleArc.EndpointWidth.leftA_membership (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    circlePt c (e 0) (e 1) r (-a) ∈
        circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b) ↔
      φ + a ≤ b ∨ 2 * Real.pi ≤ a + b + φ := by
  constructor
  · intro hm
    by_cases hw : 2 * Real.pi ≤ a + b + φ
    · exact Or.inr hw
    · have hspan : max (-a) (φ + b) - min (-a) (φ - b) < 2 * Real.pi :=
        span_of_bounds _ _ _ _ (by positivity) (by linarith)
          (by linarith) (by linarith)
      have ht := (point_mem_arc_iff_of_span c e he r hr (-a) (φ - b) (φ + b) hspan).mp hm
      exact Or.inl (by linarith [ht.1])
  · intro hm
    rcases hm with hprimary | hwrap
    · exact ⟨-a, ⟨by linarith, by linarith⟩, rfl⟩
    · refine ⟨-a + 2 * Real.pi, ⟨by linarith, by linarith⟩, ?_⟩
      simp only [circlePt, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem CircleArc.EndpointWidth.rightA_membership (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    circlePt c (e 0) (e 1) r a ∈
        circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b) ↔
      φ - b ≤ a ∧ a ≤ φ + b := by
  apply point_mem_arc_iff_of_span c e he r hr
  exact span_of_bounds _ _ _ _ (by positivity) (by linarith)
    (by linarith) (by linarith)

private theorem CircleArc.EndpointWidth.leftB_membership (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    circlePt c (e 0) (e 1) r (φ - b) ∈
        circlePt c (e 0) (e 1) r '' Set.Icc (-a) a ↔
      -a ≤ φ - b ∧ φ - b ≤ a := by
  apply point_mem_arc_iff_of_span c e he r hr
  exact span_of_bounds _ _ _ _ (by positivity) (by linarith)
    (by linarith) (by linarith)

private theorem CircleArc.EndpointWidth.rightB_membership (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    circlePt c (e 0) (e 1) r (φ + b) ∈
        circlePt c (e 0) (e 1) r '' Set.Icc (-a) a ↔
      φ + b ≤ a ∨ 2 * Real.pi ≤ a + b + φ := by
  constructor
  · intro hm
    by_cases hw : 2 * Real.pi ≤ a + b + φ
    · exact Or.inr hw
    · have hspan : max (φ + b) a - min (φ + b) (-a) < 2 * Real.pi :=
        span_of_bounds _ _ _ _ (by positivity) (by linarith)
          (by linarith) (by linarith)
      have ht := (point_mem_arc_iff_of_span c e he r hr (φ + b) (-a) a hspan).mp hm
      exact Or.inl ht.2
  · intro hm
    rcases hm with hprimary | hwrap
    · exact ⟨φ + b, ⟨by linarith, hprimary⟩, rfl⟩
    · refine ⟨φ + b - 2 * Real.pi, ⟨by linarith, by linarith⟩, ?_⟩
      simp only [circlePt, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

private def CircleArc.EndpointWidth.actualCountA (c : E3) (e : Fin 2 → E3) (r a b φ : ℝ) : ℕ :=
  countTwo (circlePt c (e 0) (e 1) r (-a) ∈
      circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))
    (circlePt c (e 0) (e 1) r a ∈
      circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))

private def CircleArc.EndpointWidth.actualCountB (c : E3) (e : Fin 2 → E3) (r a b φ : ℝ) : ℕ :=
  countTwo (circlePt c (e 0) (e 1) r (φ - b) ∈
      circlePt c (e 0) (e 1) r '' Set.Icc (-a) a)
    (circlePt c (e 0) (e 1) r (φ + b) ∈
      circlePt c (e 0) (e 1) r '' Set.Icc (-a) a)

private theorem CircleArc.EndpointWidth.actual_counts_eq (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    actualCountA c e r a b φ = countA a b φ ∧
    actualCountB c e r a b φ = countB a b φ := by
  simp only [actualCountA, actualCountB, countA, countB,
    leftA_membership c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ,
    rightA_membership c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ,
    leftB_membership c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ,
    rightB_membership c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ, and_self]

private theorem CircleArc.EndpointWidth.common_measure_of_counts (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hA : countA a b φ = 2) (hB : countB a b φ = 2) :
    ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)) =
      (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) a) ∪
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) (φ + b - 2 * Real.pi))) ∧
    Disjoint (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) a)
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) (φ + b - 2 * Real.pi)) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
      ENNReal.ofReal (r * (2 * a + 2 * b - 2 * Real.pi)) := by
  have hw := common_of_counts a b φ ha0 haπ hb0 hbπ hφ0 hφπ hA hB
  have h := CircleArc.periodicIntersectionCommon c e he r hr a b φ
    ha0 haπ hb0 hbπ hφ0 hφπ hw
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

private theorem CircleArc.EndpointWidth.ncard_pair_inter {α : Type*} (p q : α) (S : Set α) (hpq : p ≠ q) :
    (({p, q} : Set α) ∩ S).ncard = countTwo (p ∈ S) (q ∈ S) := by
  classical
  by_cases hp : p ∈ S <;> by_cases hq : q ∈ S
  · have hset : ({p, q} : Set α) ∩ S = {p, q} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · rintro (rfl | rfl) <;> simp_all
    rw [hset, Set.ncard_pair hpq]
    simp [countTwo, hp, hq]
  · have hset : ({p, q} : Set α) ∩ S = {p} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact False.elim (hq (h ▸ hx))
      · rintro rfl
        exact ⟨Or.inl rfl, hp⟩
    rw [hset, Set.ncard_singleton]
    simp [countTwo, hp, hq]
  · have hset : ({p, q} : Set α) ∩ S = {q} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact False.elim (hp (h ▸ hx))
        · exact h
      · rintro rfl
        exact ⟨Or.inr rfl, hq⟩
    rw [hset, Set.ncard_singleton]
    simp [countTwo, hp, hq]
  · have hset : ({p, q} : Set α) ∩ S = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      apply iff_false_intro
      rintro ⟨h | h, hx⟩
      · exact hp (h ▸ hx)
      · exact hq (h ▸ hx)
    rw [hset, Set.ncard_empty]
    simp [countTwo, hp, hq]

private theorem CircleArc.EndpointWidth.arcEndpoints_ne (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (z a : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) :
    circlePt c (e 0) (e 1) r (z - a) ≠
      circlePt c (e 0) (e 1) r (z + a) := by
  intro heq
  have hl : z - a ≤ z + a := by linarith
  have hspan : max (z - a) (z + a) - min (z - a) (z + a) < 2 * Real.pi := by
    rw [max_eq_right hl, min_eq_left hl]
    linarith
  have hm : circlePt c (e 0) (e 1) r (z - a) ∈
      circlePt c (e 0) (e 1) r '' Set.Icc (z + a) (z + a) :=
    ⟨z + a, ⟨le_rfl, le_rfl⟩, heq.symm⟩
  have h := (point_mem_arc_iff_of_span c e he r hr (z - a) (z + a) (z + a) hspan).mp hm
  linarith [h.1]

private theorem CircleArc.EndpointWidth.retainedA_ncard (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) :
    (({circlePt c (e 0) (e 1) r (-a), circlePt c (e 0) (e 1) r a} : Set E3) ∩
      (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))).ncard =
        actualCountA c e r a b φ := by
  apply ncard_pair_inter
  simpa only [zero_sub, zero_add] using arcEndpoints_ne c e he r hr 0 a ha0 haπ

private theorem CircleArc.EndpointWidth.retainedB_ncard (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (hb0 : 0 < b) (hbπ : b < Real.pi) :
    (({circlePt c (e 0) (e 1) r (φ - b), circlePt c (e 0) (e 1) r (φ + b)} : Set E3) ∩
      (circlePt c (e 0) (e 1) r '' Set.Icc (-a) a)).ncard =
        actualCountB c e r a b φ := by
  exact ncard_pair_inter _ _ _ (arcEndpoints_ne c e he r hr φ b hb0 hbπ)

private def CircleArc.EndpointWidth.supportedCounts (nA nB : ℕ) : Prop :=
  (nA = 1 ∧ nB = 1) ∨ (nA = 2 ∧ nB = 0) ∨ (nA = 0 ∧ nB = 2) ∨
    (nA = 0 ∧ nB = 0) ∨ (nA = 2 ∧ nB = 2)

private def CircleArc.EndpointWidth.widthFormula (nA nB : ℕ) (a b φ : ℝ) : ℝ :=
  (nA : ℝ) * a + (nB : ℝ) * b -
    (if nA = 1 ∧ nB = 1 then φ else 0) -
    (if nA = 2 ∧ nB = 2 then 2 * Real.pi else 0)

private theorem CircleArc.EndpointWidth.toReal_width_of_measure (μ : ENNReal) (r w : ℝ)
    (hr : 0 < r) (hw : 0 ≤ w) (hm : μ = ENNReal.ofReal (r * w)) :
    μ.toReal / r = w := by
  rw [hm, ENNReal.toReal_ofReal (mul_nonneg (le_of_lt hr) hw)]
  field_simp

private theorem CircleArc.EndpointWidth.width_of_actual_counts (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hcounts : supportedCounts (actualCountA c e r a b φ) (actualCountB c e r a b φ)) :
    (arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)))).toReal / r =
      widthFormula (actualCountA c e r a b φ) (actualCountB c e r a b φ) a b φ := by
  obtain ⟨hAEq, hBEq⟩ := actual_counts_eq c e he r hr a b φ
    ha0 haπ hb0 hbπ hφ0 hφπ
  rw [hAEq, hBEq] at hcounts ⊢
  rcases hcounts with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · have h := bulk_measure_of_counts c e he r hr a b φ
      ha0 haπ hb0 hbπ hφ0 hφπ hA hB
    have hbnd := bulk_of_counts a b φ ha0 haπ hb0 hbπ hφ0 hφπ hA hB
    have hw := toReal_width_of_measure _ r (a + b - φ) hr (by linarith [hbnd.2.1]) h.2
    simpa [widthFormula, hA, hB] using hw
  · have h := containsA_measure_of_counts c e he r hr a b φ
      ha0 haπ hb0 hbπ hφ0 hφπ hA hB
    have hm : arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
        ENNReal.ofReal (r * (2 * a)) := by
      rw [h.2]
      congr 1
      ring
    have hw := toReal_width_of_measure _ r (2 * a) hr (by positivity) hm
    simpa [widthFormula, hA, hB] using hw
  · have h := containsB_measure_of_counts c e he r hr a b φ
      ha0 haπ hb0 hbπ hφ0 hφπ hA hB
    have hm : arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b))) =
        ENNReal.ofReal (r * (2 * b)) := by
      rw [h.2]
      congr 1
      ring
    have hw := toReal_width_of_measure _ r (2 * b) hr (by positivity) hm
    simpa [widthFormula, hA, hB] using hw
  · have h := empty_measure_of_counts c e he r hr a b φ
      ha0 haπ hb0 hbπ hφ0 hφπ hA hB
    simp [h.2, widthFormula, hA, hB]
  · have h := common_measure_of_counts c e he r hr a b φ
      ha0 haπ hb0 hbπ hφ0 hφπ hA hB
    have hw0 := common_of_counts a b φ ha0 haπ hb0 hbπ hφ0 hφπ hA hB
    have hw := toReal_width_of_measure _ r (2 * a + 2 * b - 2 * Real.pi) hr
      (by linarith) h.2.2
    simpa [widthFormula, hA, hB] using hw

private theorem CircleArc.EndpointWidth.width_with_regime (c : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b φ : ℝ)
    (ha0 : 0 < a) (haπ : a < Real.pi) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) (bulk : Prop) [Decidable bulk]
    (hcounts : supportedCounts (actualCountA c e r a b φ) (actualCountB c e r a b φ))
    (hbulk : bulk ↔ actualCountA c e r a b φ = 1 ∧ actualCountB c e r a b φ = 1) :
    (arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-a) a) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - b) (φ + b)))).toReal / r =
      (actualCountA c e r a b φ : ℝ) * a +
      (actualCountB c e r a b φ : ℝ) * b -
      (if bulk then φ else 0) -
      (if ¬bulk ∧ actualCountA c e r a b φ ≠ 0 ∧ actualCountB c e r a b φ ≠ 0
        then 2 * Real.pi else 0) := by
  classical
  rw [width_of_actual_counts c e he r hr a b φ ha0 haπ hb0 hbπ hφ0 hφπ hcounts]
  rcases hcounts with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  all_goals simp [widthFormula, hbulk, hA, hB]

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_count_regime (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    (i j : Fin 4) :
    CircleArc.EndpointWidth.supportedCounts (nRet c (oth2 i j)) (nRet c (oth1 i j)) ∧
      (0 < P4poly X Y s ↔ nRet c (oth2 i j) = 1 ∧ nRet c (oth1 i j) = 1) := by
  have hA := nRet_coordinate_selector c X Y s hc hP (oth2 i j)
  have hB := nRet_coordinate_selector c X Y s hc hP (oth1 i j)
  by_cases hb : 0 < P4poly X Y s
  · rw [if_pos hb] at hA hB
    simp [CircleArc.EndpointWidth.supportedCounts, hA, hB, hb]
  · rw [if_neg hb] at hA hB
    by_cases ha : Apoly X Y s (oth2 i j) < 0 <;>
      by_cases hh : Apoly X Y s (oth1 i j) < 0 <;>
      simp [CircleArc.EndpointWidth.supportedCounts, hA, hB, hb, ha, hh]

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SphereGeom
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ} {i j : Fin 4}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_endpointA_set (M : P3PairCosModel c i j) :
    (Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1) ∩
      Metric.sphere (c (oth1 i j)) 1 =
      {M.point (-betaA c i j (oth1 i j)), M.point (betaA c i j (oth1 i j))} := by
  have he := p3_circle_cos_endpoint_image ((1/2:ℝ) • (c i+c j)) (M.e 0) (M.e 1)
    (Real.sqrt (1-q c i j/4)) (betaA c i j (oth1 i j)) 0
  simp only [zero_sub, zero_add, sub_zero] at he
  change M.point '' {t | Real.cos t = Real.cos (betaA c i j (oth1 i j))} =
    {M.point (-betaA c i j (oth1 i j)), M.point (betaA c i j (oth1 i j))} at he
  rw [← he]
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    rw [p3_model_spheres c i j M] at hx
    obtain ⟨t, ht, htx⟩ := hx
    refine ⟨t, (M.sphereA t).mp ?_, htx⟩
    change M.point t ∈ Metric.sphere (c (oth1 i j)) 1
    rwa [htx]
  · rintro ⟨t, ht, rfl⟩
    exact ⟨p3_model_point_on_spheres c i j M t, (M.sphereA t).mpr ht⟩

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_endpointB_set (M : P3PairCosModel c i j) :
    (Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1) ∩
      Metric.sphere (c (oth2 i j)) 1 =
      {M.point (phiE c i j - betaA c i j (oth2 i j)),
       M.point (phiE c i j + betaA c i j (oth2 i j))} := by
  have he := p3_circle_cos_endpoint_image ((1/2:ℝ) • (c i+c j)) (M.e 0) (M.e 1)
    (Real.sqrt (1-q c i j/4)) (betaA c i j (oth2 i j)) (phiE c i j)
  change M.point '' {t | Real.cos (t - phiE c i j) = Real.cos (betaA c i j (oth2 i j))} =
    {M.point (phiE c i j - betaA c i j (oth2 i j)),
      M.point (phiE c i j + betaA c i j (oth2 i j))} at he
  rw [← he]
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    rw [p3_model_spheres c i j M] at hx
    obtain ⟨t, ht, htx⟩ := hx
    refine ⟨t, (M.sphereB t).mp ?_, htx⟩
    change M.point t ∈ Metric.sphere (c (oth2 i j)) 1
    rwa [htx]
  · rintro ⟨t, ht, rfl⟩
    exact ⟨p3_model_point_on_spheres c i j M t, (M.sphereB t).mpr ht⟩

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_triple_spheres_oth (c : Fin 4 → Pt) (i j : Fin 4) (hij : i ≠ j) :
    triplePts c (oth2 i j) =
      (Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1) ∩ Metric.sphere (c (oth1 i j)) 1 ∧
    triplePts c (oth1 i j) =
      (Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1) ∩ Metric.sphere (c (oth2 i j)) 1 := by
  have hp := p3_others i j hij
  constructor
  · ext x
    simp only [triplePts, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_sphere]
    constructor
    · intro h
      exact ⟨⟨h i hp.2.2.1.symm, h j hp.2.2.2.1.symm⟩, h (oth1 i j) hp.2.2.2.2⟩
    · rintro ⟨⟨hi, hj⟩, hk⟩ n hn
      rcases p3_indices_cover i j n hij with rfl | rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
      · exact (hn rfl).elim
  · ext x
    simp only [triplePts, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_sphere]
    constructor
    · intro h
      exact ⟨⟨h i hp.1.symm, h j hp.2.1.symm⟩, h (oth2 i j) hp.2.2.2.2.symm⟩
    · rintro ⟨⟨hi, hj⟩, hk⟩ n hn
      rcases p3_indices_cover i j n hij with rfl | rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact (hn rfl).elim
      · exact hk

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_triple_K_remaining (c : Fin 4 → Pt) (l : Fin 4) :
    triplePts c l ∩ Kset c = triplePts c l ∩ Metric.closedBall (c l) 1 := by
  ext x
  constructor
  · rintro ⟨ht, hK⟩
    exact ⟨ht, Set.mem_iInter.1 (Set.mem_iInter.1 hK l) (Finset.mem_univ _)⟩
  · rintro ⟨ht, hl⟩
    refine ⟨ht, ?_⟩
    apply Set.mem_iInter.2
    intro n
    apply Set.mem_iInter.2
    intro _
    by_cases hn : n = l
    · simpa [hn] using hl
    · exact Metric.mem_closedBall.2 ((ht n hn).le)

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_retainedA_set (M : P3PairCosModel c i j) (hij : i ≠ j) :
    triplePts c (oth2 i j) ∩ Kset c =
      {M.point (-betaA c i j (oth1 i j)), M.point (betaA c i j (oth1 i j))} ∩ M.arcB := by
  rw [p3_triple_K_remaining, (p3_triple_spheres_oth c i j hij).1]
  rw [← p3_model_ballB_set c i j M, ← p3_model_endpointA_set M]
  ext x
  simp only [Set.mem_inter_iff]
  tauto

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_retainedB_set (M : P3PairCosModel c i j) (hij : i ≠ j) :
    triplePts c (oth1 i j) ∩ Kset c =
      {M.point (phiE c i j - betaA c i j (oth2 i j)),
       M.point (phiE c i j + betaA c i j (oth2 i j))} ∩ M.arcA := by
  rw [p3_triple_K_remaining, (p3_triple_spheres_oth c i j hij).2]
  rw [← p3_model_ballA_set c i j M, ← p3_model_endpointB_set M]
  ext x
  simp only [Set.mem_inter_iff]
  tauto

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_nRet_actualCountA (M : P3PairCosModel c i j)
    (hc : IsPathConfig c X Y s) (hij : i ≠ j) :
    nRet c (oth2 i j) = CircleArc.EndpointWidth.actualCountA
      ((1/2:ℝ) • (c i+c j)) M.e (Real.sqrt (1-q c i j/4))
      (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j) := by
  have hQ : 0 < Qface c (oth2 i j) := by
    rw [← (p3_pair_Qface_eq c i j hij).1]
    exact (p3_pair_Q_pos hc i j hij).1
  rw [nRet, if_pos hQ, p3_model_retainedA_set M hij]
  exact CircleArc.EndpointWidth.retainedA_ncard ((1/2:ℝ) • (c i+c j)) M.e M.ortho
    (Real.sqrt (1-q c i j/4)) (p3_pair_radius_pos hc i j hij)
    (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j)
    M.betaA_range.1 M.betaA_range.2

private theorem HardSphereB5.Lean.Geometry.PathCore.p3_nRet_actualCountB (M : P3PairCosModel c i j)
    (hc : IsPathConfig c X Y s) (hij : i ≠ j) :
    nRet c (oth1 i j) = CircleArc.EndpointWidth.actualCountB
      ((1/2:ℝ) • (c i+c j)) M.e (Real.sqrt (1-q c i j/4))
      (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j) := by
  have hQ : 0 < Qface c (oth1 i j) := by
    rw [← (p3_pair_Qface_eq c i j hij).2]
    exact (p3_pair_Q_pos hc i j hij).2
  rw [nRet, if_pos hQ, p3_model_retainedB_set M hij]
  exact CircleArc.EndpointWidth.retainedB_ncard ((1/2:ℝ) • (c i+c j)) M.e M.ortho
    (Real.sqrt (1-q c i j/4)) (p3_pair_radius_pos hc i j hij)
    (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j)
    M.betaB_range.1 M.betaB_range.2

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_width_from_model_counts (hc : IsPathConfig c X Y s)
    (hP : P4poly X Y s ≠ 0) (i j : Fin 4) (hij : i ≠ j)
    (M : P3PairCosModel c i j)
    (hA : nRet c (oth2 i j) = CircleArc.EndpointWidth.actualCountA
      ((1/2:ℝ) • (c i+c j)) M.e (Real.sqrt (1-q c i j/4))
      (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j))
    (hB : nRet c (oth1 i j) = CircleArc.EndpointWidth.actualCountB
      ((1/2:ℝ) • (c i+c j)) M.e (Real.sqrt (1-q c i j/4))
      (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j)) :
    ell c i j = (nRet c (oth2 i j) : ℝ) * betaA c i j (oth1 i j)
        + (nRet c (oth1 i j) : ℝ) * betaA c i j (oth2 i j)
        - (if 0 < P4poly X Y s then phiE c i j else 0)
        - (if P4poly X Y s < 0 ∧ isCommon c i j then 2 * Real.pi else 0) := by
  have hr := p3_pair_radius_pos hc i j hij
  have hreg := p3_pair_count_regime hc hP i j
  rw [hA, hB] at hreg
  have hw := CircleArc.EndpointWidth.width_with_regime
    ((1/2:ℝ) • (c i+c j)) M.e M.ortho (Real.sqrt (1-q c i j/4)) hr
    (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j)
    M.betaA_range.1 M.betaA_range.2 M.betaB_range.1 M.betaB_range.2
    M.phi_range.1 M.phi_range.2 (0 < P4poly X Y s) hreg.1 hreg.2
  rw [← hA, ← hB] at hw
  change (SphereGeom.arcMeasure (M.arcA ∩ M.arcB)).toReal /
    Real.sqrt (1-q c i j/4) = _ at hw
  unfold ell
  rw [p3_model_locus c i j hij M]
  by_cases hb : 0 < P4poly X Y s
  · have hn := not_lt_of_ge hb.le
    simpa only [hb, not_true_eq_false, false_and, if_false, hn, true_and, if_true,
      sub_zero] using hw
  · have hs : P4poly X Y s < 0 := lt_of_le_of_ne (le_of_not_gt hb) hP
    simpa [hb, hs, isCommon, and_comm, and_left_comm, and_assoc] using hw

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem HardSphereB5.Lean.Geometry.PathCore.pair_width (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) :
    ell c i j = (nRet c (oth2 i j) : ℝ) * betaA c i j (oth1 i j)
        + (nRet c (oth1 i j) : ℝ) * betaA c i j (oth2 i j)
        - (if 0 < P4poly X Y s then phiE c i j else 0)
        - (if P4poly X Y s < 0 ∧ isCommon c i j then 2 * Real.pi else 0) := by
  obtain ⟨M⟩ := p3_exists_cos_model hc i j hij
  have hA := p3_nRet_actualCountA M hc hij
  have hB := p3_nRet_actualCountB M hc hij
  exact p3_pair_width_from_model_counts hc hP i j hij M hA hB

private theorem HardSphereB5.Lean.Geometry.PathCore.near_moving_point_width (hc : IsPathConfig c X Y s) (hs0 : 0 < s)
    (hs : s < 1) (hP : P4poly X Y s ≠ 0) :
    phiE c 2 3 = atan2 (2 * Real.sqrt (s * Hpoly X Y s))
        (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ∧
    (0 < P4poly X Y s → ell c 2 3 =
      atan2 (2 * Real.sqrt (Qpoly X Y s 1)) (Real.sqrt s * (1 + Y - s)) +
        atan2 (2 * Real.sqrt (Qpoly X Y s 0)) (Real.sqrt s * (1 + X - s)) - phiE c 2 3) ∧
    (P4poly X Y s < 0 → Y < X → ell c 2 3 =
      2 * atan2 (2 * Real.sqrt (Qpoly X Y s 1)) (Real.sqrt s * (1 + Y - s))) ∧
    (P4poly X Y s < 0 → X < Y → ell c 2 3 =
      2 * atan2 (2 * Real.sqrt (Qpoly X Y s 0)) (Real.sqrt s * (1 + X - s))) := by
  have hWidth : P4poly X Y s ≠ 0 →
      ell c 2 3 = (nRet c 1 : ℝ) * betaA c 2 3 0 +
        (nRet c 0 : ℝ) * betaA c 2 3 1 -
        (if 0 < P4poly X Y s then phiE c 2 3 else 0) -
        (if P4poly X Y s < 0 ∧ isCommon c 2 3 then 2 * Real.pi else 0) := by
    intro hp
    have h23 := pair_width hc hp 2 3 (by decide)
    have ho1 : oth1 (2:Fin 4) 3 = 0 := by
      simp [oth1, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide]
    have ho2 : oth2 (2:Fin 4) 3 = 1 := by norm_num [oth2]
    simpa only [ho1, ho2] using h23
  exact p3_near_moving_point_width_of_pair23 hc hs (p3_near_counts hc hs) hWidth

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p3b_sliver_nonzero_count_two (hc : IsPathConfig c X Y s)
    (hP : P4poly X Y s < 0) (l : Fin 4) (hn : nRet c l ≠ 0) : nRet c l = 2 := by
  have he := nRet_coordinate_selector c X Y s hc (ne_of_lt hP) l
  rw [if_neg (not_lt_of_ge hP.le)] at he
  by_cases ha : Apoly X Y s l < 0
  · simpa only [ha, if_true] using he
  · simp only [ha, if_false] at he
    exact (hn he).elim

private theorem HardSphereB5.Lean.Geometry.PathCore.common_pair_halfwidth_sum (hc : IsPathConfig c X Y s)
    (hP : P4poly X Y s < 0) (i j : Fin 4) (hij : i ≠ j) (hcom : isCommon c i j) :
    Real.pi < betaA c i j (oth1 i j) + betaA c i j (oth2 i j) := by
  obtain ⟨M⟩ := p3_exists_cos_model hc i j hij
  have hr := p3_pair_radius_pos hc i j hij
  have hnA := p3b_sliver_nonzero_count_two hc hP (oth2 i j) hcom.2
  have hnB := p3b_sliver_nonzero_count_two hc hP (oth1 i j) hcom.1
  have hretA := p3_nRet_actualCountA M hc hij
  have hretB := p3_nRet_actualCountB M hc hij
  obtain ⟨hcntA, hcntB⟩ := CircleArc.EndpointWidth.actual_counts_eq
    ((1/2:ℝ) • (c i+c j)) M.e M.ortho (Real.sqrt (1-q c i j/4)) hr
    (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j)
    M.betaA_range.1 M.betaA_range.2 M.betaB_range.1 M.betaB_range.2
    M.phi_range.1 M.phi_range.2
  have hA : CircleArc.EndpointWidth.countA (betaA c i j (oth1 i j))
      (betaA c i j (oth2 i j)) (phiE c i j) = 2 := by
    rw [← hcntA, ← hretA]
    exact hnA
  have hB : CircleArc.EndpointWidth.countB (betaA c i j (oth1 i j))
      (betaA c i j (oth2 i j)) (phiE c i j) = 2 := by
    rw [← hcntB, ← hretB]
    exact hnB
  have hwrap := CircleArc.EndpointWidth.common_of_counts
    (betaA c i j (oth1 i j)) (betaA c i j (oth2 i j)) (phiE c i j)
    M.betaA_range.1 M.betaA_range.2 M.betaB_range.1 M.betaB_range.2
    M.phi_range.1 M.phi_range.2 hA hB
  linarith [M.phi_range.2]

private lemma HardSphereB5.Lean.Geometry.PathCore.p3b_adjacent02_acute (hc : IsPathConfig c X Y s) :
    betaA c 0 2 1 < Real.pi / 2 := by
  have h21 : q c 2 1 = X := (p3_q_symm 2 1).trans hc.q12
  have hden : Real.sqrt (q c 0 2) * (q c 0 1 + q c 2 1 - q c 0 2) = X := by
    rw [hc.q02, hc.q01, h21, Real.sqrt_one]
    ring
  unfold betaA atan2
  apply Complex.arg_lt_pi_div_two_iff.mpr
  left
  change 0 < Real.sqrt (q c 0 2) * (q c 0 1 + q c 2 1 - q c 0 2)
  rw [hden]
  exact hc.X_pos

private lemma HardSphereB5.Lean.Geometry.PathCore.p3b_adjacent13_acute (hc : IsPathConfig c X Y s) :
    betaA c 1 3 0 < Real.pi / 2 := by
  have h10 : q c 1 0 = 1 := (p3_q_symm 1 0).trans hc.q01
  have h30 : q c 3 0 = Y := (p3_q_symm 3 0).trans hc.q03
  have hden : Real.sqrt (q c 1 3) * (q c 1 0 + q c 3 0 - q c 1 3) = Y := by
    rw [hc.q13, h10, h30, Real.sqrt_one]
    ring
  unfold betaA atan2
  apply Complex.arg_lt_pi_div_two_iff.mpr
  left
  change 0 < Real.sqrt (q c 1 3) * (q c 1 0 + q c 3 0 - q c 1 3)
  rw [hden]
  exact hc.Y_pos

private theorem HardSphereB5.Lean.Geometry.PathCore.near_common_pair_acute_obtuse_s5proof (hc : IsPathConfig c X Y s)
    (hs : s < 1) (hP : P4poly X Y s < 0) :
    (Y < X → betaA c 0 2 1 < Real.pi / 2 ∧ Real.pi / 2 < betaA c 0 2 3) ∧
    (X < Y → betaA c 1 3 0 < Real.pi / 2 ∧ Real.pi / 2 < betaA c 1 3 2) := by
  constructor
  · intro hyx
    have hcom := ((sliver_table hc hP).1 hs hyx).2
    have hsum := common_pair_halfwidth_sum hc hP 0 2 (by decide) hcom
    have ho1 : oth1 (0:Fin 4) 2 = 1 := by norm_num [oth1, Fin.ext_iff]
    have ho2 : oth2 (0:Fin 4) 2 = 3 := by norm_num [oth2, oth1, Fin.ext_iff]
    rw [ho1, ho2] at hsum
    have ha := p3b_adjacent02_acute hc
    exact ⟨ha, by linarith⟩
  · intro hxy
    have hcom := ((sliver_table hc hP).2.1 hs hxy).2
    have hsum := common_pair_halfwidth_sum hc hP 1 3 (by decide) hcom
    have ho1 : oth1 (1:Fin 4) 3 = 0 := by norm_num [oth1, Fin.ext_iff]
    have ho2 : oth2 (1:Fin 4) 3 = 2 := by norm_num [oth2, oth1, Fin.ext_iff]
    rw [ho1, ho2] at hsum
    have ha := p3b_adjacent13_acute hc
    exact ⟨ha, by linarith⟩

private theorem HardSphereB5.Lean.Geometry.PathCore.near_pair23_halfwidths_acute (hc : IsPathConfig c X Y s) (hs : s < 1) :
    betaA c 2 3 0 < Real.pi / 2 ∧ betaA c 2 3 1 < Real.pi / 2 := by
  exact p3_near_betaA_acute hc hs

open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_Lean_Geometry_PathCore_near_common_pair_acute_obtuse : ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s)
    (hs : s < 1) (hP : P4poly X Y s < 0),
  (Y < X → betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3) ∧
    (X < Y → betaA c 1 3 0 < π / 2 ∧ π / 2 < betaA c 1 3 2) := by
  exact @HardSphereB5.Lean.Geometry.PathCore.near_common_pair_acute_obtuse_s5proof
