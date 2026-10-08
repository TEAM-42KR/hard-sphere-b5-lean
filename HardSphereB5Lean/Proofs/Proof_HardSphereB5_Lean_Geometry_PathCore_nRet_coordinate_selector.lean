import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 3000000

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

#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_signs_near_gt
#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_signs_near_lt
#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_signs_far
#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_s_ne_one
#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_near_ne_diagonal
#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_exactly_one

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

#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_table_of_selector
#print axioms HardSphereB5.Lean.Geometry.PathCore.sliver_incidence_of_selector
#print axioms HardSphereB5.Lean.Geometry.PathCore.lemma64d_of_incidence

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

theorem proof_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector (c : Fin 4 → Pt) (X Y s : ℝ)
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

example (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (l : Fin 4) :
    nRet c l = if 0 < P4poly X Y s then 1 else if Apoly X Y s l < 0 then 2 else 0 :=
  proof_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector c X Y s hc hP l

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_nRet_coordinate_selector
