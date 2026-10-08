import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_area_eq_polar_sectors
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_sector_area_primitive
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_cap_arc_azimuth_increment
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_sector_width_sum
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_capCorner_gamma
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_capCorner_pos_smul
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_aligned_area_integral
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_area_sectors_boundary_sum
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_wrapWindow_integral_any
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Bridge_profile_patch_measure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_profile_of_unit_oriented
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_cap_circle_polar_chart_ordered
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_alignedCap_exists
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_profile_of_unit
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_BulkMatching
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_BulkCalculus_BC_frameTangent
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Definitions.Def_Gnomonic_inverseNorth
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cross_vec_triple
import HardSphereB5Lean.Theorems.Thm_Gnomonic_integralFrame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_indicator_integrable
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
import HardSphereB5Lean.Theorems.Thm_CircleArc_pair_circle_on_spheres
import HardSphereB5Lean.Theorems.Thm_CircleArc_ball_iff_inner
import HardSphereB5Lean.Theorems.Thm_CircleArc_intervalIntersection
import HardSphereB5Lean.Theorems.Thm_CircleArc_arcIntersectionCases
import HardSphereB5Lean.Theorems.Thm_ConvexDisk_exists_homeomorph_closedBall
import HardSphereB5Lean.Theorems.Thm_Gnomonic_capArc_regular
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_capPoint_window_image
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_ties_finite
import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_dOmega_frame
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_patch_circle_image
set_option autoImplicit false
noncomputable section
private def AS4P.scopeTag : Unit := ()
private def AS4T.scopeTag : Unit := ()
private def AS4B.scopeTag : Unit := ()
private def AS4S.scopeTag : Unit := ()
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Real
section AS4Scope0
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4T
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000
private def AS4T.sq (x : Pt) : ℝ := ⟪x, x⟫
private def AS4T.faceDelta (v w : Pt) : ℝ := DeltaT (sq v) (sq w) (sq (v - w))
private def AS4T.faceQ (v w : Pt) : ℝ := QT (sq v) (sq w) (sq (v - w))
private def AS4T.center (v w : Pt) : Pt :=
  (sq w * (sq v - sq w + sq (v - w)) / faceDelta v w) • v +
  (sq v * (sq w - sq v + sq (v - w)) / faceDelta v w) • w
private def AS4T.height (v w : Pt) : ℝ := Real.sqrt (faceQ v w / faceDelta v w)
private def AS4T.orientedNormal (v w z : Pt) : Pt :=
  if 0 < ⟪z, SphereGeom.cross v w⟫ then ‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w
  else -(‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w)
private def AS4T.triple (v w : Pt) : Set Pt := {x | ‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1}
private lemma AS4T.sq_eq_norm_sq (x : Pt) : sq x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
private lemma AS4T.sq_nonneg (x : Pt) : 0 ≤ sq x := by rw [sq_eq_norm_sq]; positivity
private lemma AS4T.sq_sub (x y : Pt) : sq (x - y) = sq x + sq y - 2 * ⟪x, y⟫ := by
  simp only [sq, inner_sub_left, inner_sub_right, real_inner_comm y x]
  ring
private lemma AS4T.sq_eq_one_iff (x : Pt) : sq x = 1 ↔ ‖x‖ = 1 := by
  rw [sq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg x]
  · intro h; rw [h]; norm_num
private lemma AS4T.inner_coords (x y : Pt) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]
private lemma AS4T.cross_coords (v w : Pt) :
    SphereGeom.cross v w = WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1,
      v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := by
  simp [SphereGeom.cross, SphereGeom.cross, cross_apply]
private lemma AS4T.cross_v (v w : Pt) : ⟪v, SphereGeom.cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma AS4T.cross_w (v w : Pt) : ⟪w, SphereGeom.cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma AS4T.cross_sq (v w : Pt) :
    sq (SphereGeom.cross v w) = sq v * sq w - ⟪v, w⟫ ^ 2 := by
  simp only [sq, inner_coords, cross_coords]
  simp
  ring
private lemma AS4T.gram_resolution (v w x : Pt) :
    (sq v * sq w - ⟪v, w⟫ ^ 2) • x =
      (sq w * ⟪v, x⟫ - ⟪v, w⟫ * ⟪w, x⟫) • v +
      (sq v * ⟪w, x⟫ - ⟪v, w⟫ * ⟪v, x⟫) • w +
      ⟪SphereGeom.cross v w, x⟫ • SphereGeom.cross v w := by
  simp only [sq, inner_coords]
  ext i
  fin_cases i <;> simp [cross_coords] <;> ring
private lemma AS4T.delta_gram (v w : Pt) :
    faceDelta v w = 4 * (sq v * sq w - ⟪v, w⟫ ^ 2) := by
  simp only [faceDelta, DeltaT, sq_sub]
  ring
private lemma AS4T.q_delta (v w : Pt) :
    faceQ v w = faceDelta v w - sq v * sq w * sq (v - w) := rfl
private lemma AS4T.center_inner_v (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, v⟫ = sq v / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq, real_inner_comm w v]
  ring
private lemma AS4T.center_inner_w (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, w⟫ = sq w / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq]
  ring
private lemma AS4T.center_sq (v w : Pt) (hD : faceDelta v w ≠ 0) :
    sq (center v w) = sq v * sq w * sq (v - w) / faceDelta v w := by
  change ⟪center v w, center v w⟫ = _
  nth_rw 2 [center]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    center_inner_v v w hD, center_inner_w v w hD]
  ring
private lemma AS4T.cross_norm_pos (v w : Pt) (hD : 0 < faceDelta v w) : 0 < ‖SphereGeom.cross v w‖ := by
  have he := delta_gram v w
  have hs := cross_sq v w
  rw [sq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (SphereGeom.cross v w)]
private lemma AS4T.unit_cross_norm (v w : Pt) (hD : 0 < faceDelta v w) :
    ‖‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cross_norm_pos v w hD))]
  exact inv_mul_cancel₀ (ne_of_gt (cross_norm_pos v w hD))
private lemma AS4T.normal_norm (v w z : Pt) (hD : 0 < faceDelta v w) :
    ‖orientedNormal v w z‖ = 1 := by
  unfold orientedNormal
  split_ifs <;> simp only [norm_neg, unit_cross_norm v w hD]
private lemma AS4T.normal_sq (v w z : Pt) (hD : 0 < faceDelta v w) :
    sq (orientedNormal v w z) = 1 := by
  rw [sq_eq_norm_sq, normal_norm v w z hD]; norm_num
private lemma AS4T.normal_v (v w z : Pt) : ⟪v, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_v]
private lemma AS4T.normal_w (v w z : Pt) : ⟪w, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_w]
private lemma AS4T.normal_oriented (v w z : Pt) (hD : 0 < faceDelta v w)
    (hG : ⟪z, SphereGeom.cross v w⟫ ≠ 0) : 0 < ⟪z, orientedNormal v w z⟫ := by
  have hi := inv_pos.mpr (cross_norm_pos v w hD)
  unfold orientedNormal
  split_ifs with hz
  · rw [real_inner_smul_right]; exact mul_pos hi hz
  · rw [inner_neg_right, real_inner_smul_right]
    have hz' : ⟪z, SphereGeom.cross v w⟫ < 0 := lt_of_le_of_ne (le_of_not_gt hz) hG
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hi hz')
private lemma AS4T.center_normal (v w z : Pt) : ⟪center v w, orientedNormal v w z⟫ = 0 := by
  simp only [center, inner_add_left, real_inner_smul_left, normal_v, normal_w,
    mul_zero, add_zero]
private lemma AS4T.perp_as_normal (v w z d : Pt) (hD : 0 < faceDelta v w)
    (hv : ⟪v, d⟫ = 0) (hw : ⟪w, d⟫ = 0) :
    d = ⟪orientedNormal v w z, d⟫ • orientedNormal v w z := by
  have hn := ne_of_gt (cross_norm_pos v w hD)
  have hsn : sq (SphereGeom.cross v w) ≠ 0 := by
    rw [sq_eq_norm_sq]; exact pow_ne_zero 2 hn
  have hr := gram_resolution v w d
  rw [← cross_sq, hv, hw] at hr
  simp only [mul_zero, sub_self, zero_smul, zero_add] at hr
  have hd : d = (⟪SphereGeom.cross v w, d⟫ / sq (SphereGeom.cross v w)) • SphereGeom.cross v w := by
    calc
      d = (sq (SphereGeom.cross v w))⁻¹ • (sq (SphereGeom.cross v w) • d) := by
        rw [smul_smul, inv_mul_cancel₀ hsn, one_smul]
      _ = (⟪SphereGeom.cross v w, d⟫ / sq (SphereGeom.cross v w)) • SphereGeom.cross v w := by
        rw [hr, smul_smul]; congr 1; ring
  have hc : d = ⟪‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w, d⟫ • (‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w) := by
    calc
      d = (⟪SphereGeom.cross v w, d⟫ / sq (SphereGeom.cross v w)) • SphereGeom.cross v w := hd
      _ = ⟪‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w, d⟫ • (‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w) := by
        rw [real_inner_smul_left, smul_smul]
        congr 1
        rw [sq_eq_norm_sq]
        field_simp [hn]
  unfold orientedNormal
  split_ifs
  · exact hc
  · simpa only [inner_neg_left, neg_smul, smul_neg, neg_neg] using hc
private lemma AS4T.height_pos (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    0 < height v w := Real.sqrt_pos.mpr (div_pos hQ hD)
private lemma AS4T.center_height (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    sq (center v w) + height v w ^ 2 = 1 := by
  rw [center_sq v w (ne_of_gt hD)]
  unfold height
  rw [Real.sq_sqrt (le_of_lt (div_pos hQ hD)), q_delta]
  field_simp [ne_of_gt hD]
  ring
private lemma AS4T.mem_triple_iff (v w x : Pt) :
    x ∈ triple v w ↔ sq x = 1 ∧ ⟪x, v⟫ = sq v / 2 ∧ ⟪x, w⟫ = sq w / 2 := by
  change (‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1) ↔ _
  simp only [← sq_eq_one_iff, sq_sub]
  constructor
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
private lemma AS4T.center_line_sq (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w) :
    sq (center v w + r • orientedNormal v w z) = sq (center v w) + r ^ 2 := by
  have ho := center_normal v w z
  have hn : ⟪orientedNormal v w z, orientedNormal v w z⟫ = 1 := normal_sq v w z hD
  have ho' : ⟪orientedNormal v w z, center v w⟫ = 0 := (real_inner_comm (center v w) _).trans ho
  simp only [sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ho, ho', hn]
  ring
private lemma AS4T.line_mem_triple (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
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
private theorem AS4T.triple_exact (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
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
private lemma AS4T.cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z) ^ 2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z) ^ 2 -
      inner ℝ w w * (inner ℝ v z) ^ 2 -
      inner ℝ z z * (inner ℝ v w) ^ 2 := by
  change ⟪SphereGeom.cross v w, z⟫ ^ 2 = _
  simp only [inner_coords, cross_coords]
  simp
  ring
private lemma AS4T.triple_points_ne (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
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
private theorem AS4T.fourth_sq_formula (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hr : r ^ 2 = height v w ^ 2) :
    ‖center v w + r • orientedNormal v w z - z‖ ^ 2 - 1 =
      sq z - 2 * ⟪z, center v w⟫ - 2 * r * ⟪z, orientedNormal v w z⟫ := by
  rw [← sq_eq_norm_sq, sq_sub, center_line_sq v w z r hD,
    inner_add_left, real_inner_smul_left, real_inner_comm z (center v w),
    real_inner_comm z (orientedNormal v w z), hr]
  linarith [center_height v w hD hQ]
end
end AS4Scope0
section AS4Scope1
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4P
open HardSphereB5.Lean (Pt)
private lemma AS4P.q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]
private lemma AS4P.q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]
private lemma AS4P.inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith
private def AS4P.Dpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![DeltaT X 1 s, DeltaT 1 Y s, DeltaT 1 Y 1, DeltaT 1 1 X]
private def AS4P.gramPoly (a b cc d e f : ℝ) : ℝ :=
  4*a*b*d + (a+b-cc)*(a+d-e)*(b+d-f)
    - a*(b+d-f)^2 - b*(a+d-e)^2 - d*(a+b-cc)^2
private def AS4P.faceAPoly (a b cc d e f : ℝ) : ℝ :=
  DeltaT a b cc * d - b*(a-b+cc)*(a+d-e) - a*(b-a+cc)*(b+d-f)
private lemma AS4P.face_polys (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
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
private lemma AS4P.cayley_menger_face_identity (X Y s : ℝ) (l : Fin 4) :
    Apoly X Y s l ^ 2 - 4 * Hpoly X Y s * Qpoly X Y s l =
      -Dpoly X Y s l * P4poly X Y s := by
  fin_cases l <;> simp [Apoly, Hpoly, Qpoly, Dpoly, DeltaT, P4poly] <;> ring
private lemma AS4P.cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z)^2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z)^2 -
      inner ℝ w w * (inner ℝ v z)^2 -
      inner ℝ z z * (inner ℝ v w)^2 :=
  AS4T.cross_gram_identity v w z
private lemma AS4P.gram_from_q (c : Fin 4 → Pt) (i j k l : Fin 4) :
    4 * (inner ℝ (SphereGeom.cross (c j - c i) (c k - c i)) (c l - c i))^2 =
    gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) := by
  rw [cross_gram_identity, ← q_inner, ← q_inner, ← q_inner,
    inner_from_q, inner_from_q, inner_from_q]
  simp only [gramPoly]
  ring
private lemma AS4P.retained_set_eq (c : Fin 4 → Pt) (l : Fin 4) :
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
private lemma AS4P.bulk_patch_counts (c : Fin 4 → Pt) (hn : ∀ l, nRet c l = 1) :
    ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 := by
  intro m
  simp_rw [hn]
  simp
end AS4Scope1
section AS4Scope2
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4P
open HardSphereB5.Lean (Pt)
private lemma AS4P.two_point_retained_count (p m z : Pt) (a b : ℝ) (hpm : p ≠ m) (hb : 0 < b)
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
private lemma AS4P.margin_selector (H D Q P A a b : ℝ) (hH : 0 < H) (hD : 0 < D)
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
end AS4Scope2
section AS4Scope3
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4P
set_option maxHeartbeats 1000000
end AS4Scope3
section AS4Scope4
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4P
end AS4Scope4
section AS4Scope5
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4P
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
private lemma AS4P.path_s_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) : 0 < s := by
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
private lemma AS4P.path_Qpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) :
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
private lemma AS4P.q_nonneg' (c : Fin 4 → Pt) (i j : Fin 4) : 0 ≤ q c i j := by unfold q; positivity
private lemma AS4P.path_Dpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
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
private lemma AS4P.norm_sub_base (x y p : Pt) : ‖(x-p)-(y-p)‖ = ‖x-y‖ := by
  congr 1; abel
private lemma AS4P.triplePts_translate (c : Fin 4 → Pt) (l : Fin 4) :
    triplePts c l = {x | x - c (faceVerts l).1 ∈
      AS4T.triple (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1)} := by
  ext x
  fin_cases l <;>
    simp [triplePts, faceVerts, Fin.forall_fin_succ, AS4T.triple,
      dist_eq_norm, norm_sub_base] <;> tauto
private lemma AS4P.TG_sq_q (c : Fin 4 → Pt) (i j : Fin 4) : AS4T.sq (c j-c i) = q c i j := by
  exact (q_inner c i j).symm
private lemma AS4P.TG_sq_diff_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    AS4T.sq ((c j-c i)-(c k-c i)) = q c j k := by
  have he : (c j-c i)-(c k-c i) = c j-c k := by abel
  rw [he, TG_sq_q, q_symm']
private lemma AS4P.face_TG_D (c : Fin 4 → Pt) (l : Fin 4) :
    AS4T.faceDelta (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) =
    Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 := by
  simp only [AS4T.faceDelta, TG_sq_q, TG_sq_diff_q, Deltaf]
private lemma AS4P.face_TG_Q (c : Fin 4 → Pt) (l : Fin 4) :
    AS4T.faceQ (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) = Qface c l := by
  simp only [AS4T.faceQ, TG_sq_q, TG_sq_diff_q, Qface, Qf]
private lemma AS4P.normal_projection_identity (v w z : Pt) (hD : 0 < AS4T.faceDelta v w) :
    AS4T.faceDelta v w * (inner ℝ z (AS4T.orientedNormal v w z))^2 =
      4 * (inner ℝ z (SphereGeom.cross v w))^2 := by
  have hn := ne_of_gt (AS4T.cross_norm_pos v w hD)
  have hd : AS4T.faceDelta v w = 4*‖SphereGeom.cross v w‖^2 := by
    rw [AS4T.delta_gram, ← AS4T.cross_sq, AS4T.sq_eq_norm_sq]
  rw [hd]
  unfold AS4T.orientedNormal
  split_ifs <;> simp only [inner_neg_right, real_inner_smul_right]
  all_goals field_simp [hn]
  all_goals ring
private lemma AS4P.numerator_identity (v w z : Pt) (hD : AS4T.faceDelta v w ≠ 0) :
    AS4T.faceDelta v w * (AS4T.sq z - 2*inner ℝ z (AS4T.center v w)) =
      faceAPoly (AS4T.sq v) (AS4T.sq w) (AS4T.sq (v-w))
        (AS4T.sq z) (AS4T.sq (z-v)) (AS4T.sq (z-w)) := by
  simp only [AS4T.center, inner_add_right, real_inner_smul_right, faceAPoly]
  have hd : DeltaT (AS4T.sq v) (AS4T.sq w)
      (AS4T.sq (v-w)) = AS4T.faceDelta v w := rfl
  rw [hd]
  simp only [AS4T.sq_sub]
  field_simp [hD]
  rw [AS4T.delta_gram]
  ring
private theorem AS4P.nRet_coordinate_selector (c : Fin 4 → Pt) (X Y s : ℝ)
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (l : Fin 4) :
    nRet c l = if 0 < P4poly X Y s then 1 else if Apoly X Y s l < 0 then 2 else 0 := by
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  let v := c j-c i
  let w := c k-c i
  let z := c l-c i
  let D := AS4T.faceDelta v w
  let Q := AS4T.faceQ v w
  let N := AS4T.orientedNormal v w z
  let h := AS4T.height v w
  let o := AS4T.center v w
  let p := c i + (o+h•N)
  let m := c i + (o-h•N)
  let a := AS4T.sq z - 2*inner ℝ z o
  let b := 2*h*inner ℝ z N
  have hDP : D = Dpoly X Y s l := (face_TG_D c l).trans (face_polys c X Y s hc l).2.1
  have hQP : Q = Qpoly X Y s l := (face_TG_Q c l).trans (face_polys c X Y s hc l).1
  have hD : 0 < D := by rw [hDP]; exact path_Dpoly_pos c X Y s hc l
  have hQ : 0 < Q := by rw [hQP]; exact path_Qpoly_pos c X Y s hc l
  have hQface : 0 < Qface c l := by rw [← face_TG_Q c l]; exact hQ
  have hdet : 4*(inner ℝ z (SphereGeom.cross v w))^2 = Hpoly X Y s := by
    have hg := gram_from_q c i j k l
    rw [(face_polys c X Y s hc l).2.2.2] at hg
    simpa only [real_inner_comm] using hg
  have hG : inner ℝ z (SphereGeom.cross v w) ≠ 0 := by intro hz; rw [hz] at hdet; nlinarith [hc.H_pos]
  have hn : 0 < inner ℝ z N := AS4T.normal_oriented v w z hD hG
  have hh : 0 < h := AS4T.height_pos v w hD hQ
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hh) hn
  have hpm : p ≠ m := by
    exact fun he => AS4T.triple_points_ne v w z hD hQ (add_left_cancel he)
  have htr : triplePts c l = {p,m} := by
    rw [triplePts_translate c l]
    change {x | x-c i ∈ AS4T.triple v w} = {p,m}
    rw [AS4T.triple_exact v w z hD hQ]
    ext x
    simp [p,m,o,h,N,Set.mem_insert_iff,Set.mem_singleton_iff,sub_eq_iff_eq_add,add_comm]
  have hp : (dist p (c l))^2-1 = a-b := by
    have he : p-c l = o+h•N-z := by dsimp [p,z]; abel
    rw [dist_eq_norm,he]
    exact AS4T.fourth_sq_formula v w z h hD hQ rfl
  have hm : (dist m (c l))^2-1 = a+b := by
    have he : m-c l = o+(-h)•N-z := by dsimp [m,z]; simp only [neg_smul]; abel
    rw [dist_eq_norm,he,AS4T.fourth_sq_formula v w z (-h) hD hQ (neg_sq h)]
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
end AS4Scope5
section AS4Scope6
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4P
open HardSphereB5.Lean (Pt)
private theorem AS4P.bulk_incidence {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) :
    (∀ l, nRet c l = 1) ∧ ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 := by
  have hn : ∀ l, nRet c l = 1 := by
    intro l
    rw [AS4P.nRet_coordinate_selector c X Y s hc (ne_of_gt hP) l,if_pos hP]
  exact ⟨hn,bulk_patch_counts c hn⟩
end AS4Scope6
noncomputable section
open MeasureTheory Real SphereGeom
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope7
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 PositiveConvexBoundary)
private structure AS4B.B4a0 where
  c : Fin 4 → Pt
  X : ℝ
  Y : ℝ
  s : ℝ
  path : IsPathConfig c X Y s
  bulk : 0 < P4poly X Y s
private theorem AS4B.B4a131 (b : B4a0) (l : Fin 4) :
    ∃ p : Pt, triplePts b.c l ∩ Kset b.c = {p} := by
  have hn : nRet b.c l = 1 := (AS4P.bulk_incidence b.path b.bulk).1 l
  by_cases hQ : 0 < Qface b.c l
  · apply Set.ncard_eq_one.mp
    simpa only [nRet, if_pos hQ] using hn
  · simp only [nRet, if_neg hQ] at hn
    exact (Nat.zero_ne_one hn).elim
private def AS4B.B4a150 (b : B4a0) (l : Fin 4) : Pt :=
  Classical.choose (B4a131 b l)
private theorem AS4B.B4a130 (b : B4a0) (l : Fin 4) :
    triplePts b.c l ∩ Kset b.c = {B4a150 b l} :=
  Classical.choose_spec (B4a131 b l)
private theorem AS4B.B4a153 (b : B4a0) (l : Fin 4) :
    B4a150 b l ∈ triplePts b.c l ∩ Kset b.c := by
  rw [B4a130]
  exact Set.mem_singleton _
private def AS4B.B4a98 (i : Fin 4) : Fin 3 → Fin 4 :=
  ![![(1 : Fin 4),2,3], ![0,2,3], ![0,1,3], ![0,1,2]] i
private theorem AS4B.B4a100 : ∀ (i : Fin 4) (j : Fin 3), B4a98 i j ≠ i := by decide
private theorem AS4B.B4a99 : ∀ i : Fin 4, Function.Injective (B4a98 i) := by decide
private def AS4B.B4a48 (j : Fin 3) : Fin 3 := ![(0 : Fin 3),2,1] j
private theorem AS4B.B4a49 : Function.Injective B4a48 := by decide
private def AS4B.B4a94 (b : B4a0) (i : Fin 4) (j : Fin 3) : Fin 4 :=
  let o := B4a98 i
  if det3 (b.c (o 0) - b.c i) (b.c (o 1) - b.c i) (b.c (o 2) - b.c i) < 0
    then o (B4a48 j) else o j
private theorem AS4B.B4a97 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a94 b i j ≠ i := by
  dsimp only [B4a94]
  split_ifs <;> apply B4a100
private theorem AS4B.B4a96 (b : B4a0) (i : Fin 4) :
    Function.Injective (B4a94 b i) := by
  intro j k h
  dsimp only [B4a94] at h
  split_ifs at h
  · exact B4a49 (B4a99 i h)
  · exact B4a99 i h
private theorem AS4B.B4a92 : ∀ j : Fin 3, j ≠ j + 1 := by decide
private theorem AS4B.B4a91 : ∀ j : Fin 3, j ≠ (j + 1) + 1 := by decide
private def AS4B.B4a144 (b : B4a0) (i : Fin 4) (j : Fin 3) : Pt :=
  B4a150 b (B4a94 b i (j+1))
private def AS4B.B4a42 (b : B4a0) (i : Fin 4) (j : Fin 3) : Pt :=
  B4a150 b (B4a94 b i ((j+1)+1))
private theorem AS4B.B4a151 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a42 b i j = B4a144 b i (j+1) := rfl
private theorem AS4B.B4a146 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a144 b i j ∈
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1 := by
  have h := (B4a153 b (B4a94 b i (j+1))).1
  change ∀ m, m ≠ B4a94 b i (j+1) → dist (B4a144 b i j) (b.c m) = 1 at h
  have hlabel : B4a94 b i j ≠ B4a94 b i (j+1) :=
    fun heq => B4a92 j (B4a96 b i heq)
  exact ⟨h i (B4a97 b i (j+1)).symm, h _ hlabel⟩
private theorem AS4B.B4a45 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a42 b i j ∈
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1 := by
  have h := (B4a153 b (B4a94 b i ((j+1)+1))).1
  change ∀ m, m ≠ B4a94 b i ((j+1)+1) → dist (B4a42 b i j) (b.c m) = 1 at h
  have hlabel : B4a94 b i j ≠ B4a94 b i ((j+1)+1) :=
    fun heq => B4a91 j (B4a96 b i heq)
  exact ⟨h i (B4a97 b i ((j+1)+1)).symm, h _ hlabel⟩
private def AS4B.B4a89 (b : B4a0) (i : Fin 4) (j : Fin 3) : Pt :=
  (1/2 : ℝ) • (b.c i + b.c (B4a94 b i j))
private def AS4B.B4a116 (b : B4a0) (i : Fin 4) (j : Fin 3) : ℝ :=
  Real.sqrt (1 - q b.c i (B4a94 b i j) / 4)
private def AS4B.B4a10 (b : B4a0) (i : Fin 4) (j : Fin 3) : Pt :=
  (dist (b.c i) (b.c (B4a94 b i j)))⁻¹ • (b.c (B4a94 b i j) - b.c i)
private def AS4B.B4a39 (b : B4a0) (i : Fin 4) (j : Fin 3) : Pt :=
  (B4a116 b i j)⁻¹ • (B4a144 b i j - B4a89 b i j)
private def AS4B.B4a40 (b : B4a0) (i : Fin 4) (j : Fin 3) : Pt :=
  SphereGeom.cross (B4a10 b i j) (B4a39 b i j)
private def AS4B.B4a13 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) : Pt :=
  SphereGeom.circlePt (B4a89 b i j) (B4a39 b i j) (B4a40 b i j) (B4a116 b i j) t
private def AS4B.B4a75 (b : B4a0) (i : Fin 4) (j : Fin 3) : ℝ :=
  let v := B4a42 b i j - B4a89 b i j
  let a := atan2 (inner ℝ (B4a40 b i j) v) (inner ℝ (B4a39 b i j) v)
  if 0 < a then a else a + 2 * Real.pi
private theorem AS4B.B4a19 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ContDiff ℝ 2 (B4a13 b i j) := by
  unfold B4a13 SphereGeom.circlePt
  fun_prop
private def AS4B.B4a108 (b : B4a0) (i : Fin 4) (p : Pt) : E2 :=
  let u := p - b.c i
  let d := inner ℝ (B4a10 b i 0) u
  WithLp.toLp 2 ![inner ℝ (B4a39 b i 0) u / d, inner ℝ (B4a40 b i 0) u / d]
private def AS4B.B4a1 (b : B4a0) (i : Fin 4) : Set E2 := B4a108 b i '' patch b.c i
private def AS4B.B4a54 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) : E2 :=
  B4a108 b i (B4a13 b i j t)
private theorem AS4B.B4a9 (c : Fin 4 → Pt) : IsClosed (Kset c) := by
  unfold Kset body
  exact isClosed_iInter fun n => isClosed_iInter fun _ => Metric.isClosed_closedBall
private theorem AS4B.B4a104 (c : Fin 4 → Pt) (i : Fin 4) : IsCompact (patch c i) :=
  (isCompact_sphere (c i) 1).inter_right (B4a9 c)
end AS4Scope7
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope8
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 PositiveConvexBoundary)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma AS4B.B4a137 (hc : IsPathConfig c X Y s) : s < 4 := by
  have hx : dist (c 2) (c 1) ^ 2 = X := (q_symm' c 2 1).trans hc.q12
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
private lemma AS4B.B4a101 (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < q c i j ∧ q c i j < 4 := by
  have hs0 := path_s_pos c X Y s hc
  have hs4 := B4a137 hc
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
    rw [q_symm' c 1 0, hc.q01]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · exact (hij rfl).elim
  · change 0 < q c 1 2 ∧ q c 1 2 < 4
    rw [hc.q12]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 1 3 ∧ q c 1 3 < 4
    rw [hc.q13]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 2 0 ∧ q c 2 0 < 4
    rw [q_symm' c 2 0, hc.q02]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 2 1 ∧ q c 2 1 < 4
    rw [q_symm' c 2 1, hc.q12]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · exact (hij rfl).elim
  · change 0 < q c 2 3 ∧ q c 2 3 < 4
    rw [hc.q23]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 3 0 ∧ q c 3 0 < 4
    rw [q_symm' c 3 0, hc.q03]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 3 1 ∧ q c 3 1 < 4
    rw [q_symm' c 3 1, hc.q13]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · change 0 < q c 3 2 ∧ q c 3 2 < 4
    rw [q_symm' c 3 2, hc.q23]
    constructor <;> linarith [hc.X_pos, hc.Y_pos, hc.X_lt_one, hc.Y_lt_one]
  · exact (hij rfl).elim
private lemma AS4B.B4a102 (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < Real.sqrt (1 - q c i j / 4) := by
  apply Real.sqrt_pos.2
  linarith [(B4a101 hc i j hij).2]
private theorem AS4B.B4a38 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    0 < dist (b.c i) (b.c (B4a94 b i j)) ∧
    dist (b.c i) (b.c (B4a94 b i j)) < 2 := by
  have h := B4a101 b.path i (B4a94 b i j) (B4a97 b i j).symm
  have hn := dist_nonneg (x := b.c i) (y := b.c (B4a94 b i j))
  change 0 < dist (b.c i) (b.c (B4a94 b i j))^2 ∧
    dist (b.c i) (b.c (B4a94 b i j))^2 < 4 at h
  constructor <;> nlinarith [h.1, h.2]
private theorem AS4B.B4a117 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    0 < B4a116 b i j :=
  B4a102 b.path i (B4a94 b i j) (B4a97 b i j).symm
private theorem AS4B.B4a50 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    Gnomonic.CapFrame (B4a10 b i j) (B4a39 b i j) (B4a40 b i j) := by
  let v : Pt := b.c (B4a94 b i j) - b.c i
  let u : Pt := B4a144 b i j - b.c i
  let d : ℝ := dist (b.c i) (b.c (B4a94 b i j))
  let r : ℝ := B4a116 b i j
  let m : Pt := B4a144 b i j - B4a89 b i j
  have hd : 0 < d := (B4a38 b i j).1
  have hr : 0 < r := B4a117 b i j
  have hpair := B4a146 b i j
  have hu : ‖u‖ = 1 := by simpa only [u, Metric.mem_sphere, dist_eq_norm] using hpair.1
  have huw : ‖u-v‖ = 1 := by
    have he : u-v = B4a144 b i j - b.c (B4a94 b i j) := by dsimp [u,v]; abel
    rw [he]
    simpa only [Metric.mem_sphere, dist_eq_norm] using hpair.2
  have hv : inner ℝ v v = d^2 := by
    rw [real_inner_self_eq_norm_sq]
    simp only [v,d, ← dist_eq_norm, dist_comm]
  have hvn : ‖v‖^2 = d^2 := by simpa only [real_inner_self_eq_norm_sq] using hv
  have huv : inner ℝ u v = d^2/2 := by
    have he := norm_sub_sq_real u v
    rw [hu,huw,hvn] at he
    nlinarith
  have hm : m = u - (1/2 : ℝ) • v := by dsimp [m,u,v,B4a89]; module
  have hmv : inner ℝ m v = 0 := by
    rw [hm,inner_sub_left,real_inner_smul_left,huv,hv]
    ring
  have hvm : inner ℝ v m = 0 := by rw [real_inner_comm]; exact hmv
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq,hu]; norm_num
  have hvu : inner ℝ v u = d^2/2 := by rw [real_inner_comm]; exact huv
  have hmm : inner ℝ m m = 1-d^2/4 := by
    rw [hm]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
      huu,huv,hvu,hv]
    ring
  have hrr : r^2 = 1-d^2/4 := by
    change (Real.sqrt (1-d^2/4))^2 = 1-d^2/4
    apply Real.sq_sqrt
    have hq := (B4a101 b.path i (B4a94 b i j) (B4a97 b i j).symm).2
    change d^2 < 4 at hq
    linarith
  have haa : inner ℝ (B4a10 b i j) (B4a10 b i j) = 1 := by
    change inner ℝ (d⁻¹ • v) (d⁻¹ • v) = 1
    simp only [real_inner_smul_left,real_inner_smul_right,hv]
    field_simp [ne_of_gt hd]
  have he00 : inner ℝ (B4a39 b i j) (B4a39 b i j) = 1 := by
    change inner ℝ (r⁻¹ • m) (r⁻¹ • m) = 1
    simp only [real_inner_smul_left,real_inner_smul_right,hmm,← hrr]
    field_simp [ne_of_gt hr]
  have hae0 : inner ℝ (B4a10 b i j) (B4a39 b i j) = 0 := by
    change inner ℝ (d⁻¹ • v) (r⁻¹ • m) = 0
    simp only [real_inner_smul_left,real_inner_smul_right,hvm,mul_zero]
  have he11 : inner ℝ (B4a40 b i j) (B4a40 b i j) = 1 := by
    have he := AS4T.cross_sq (B4a10 b i j) (B4a39 b i j)
    change inner ℝ (B4a40 b i j) (B4a40 b i j) = _ at he
    simpa only [AS4T.sq,haa,he00,hae0,mul_one,zero_pow (by decide : (2 : ℕ) ≠ 0),sub_zero] using he
  exact ⟨haa,he00,he11,hae0,
    AS4T.cross_v _ _,AS4T.cross_w _ _⟩
private theorem AS4B.B4a52 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    Orthonormal ℝ ![B4a39 b i j,B4a40 b i j] := by
  apply orthonormal_iff_ite.mpr
  have F := B4a50 b i j
  intro a d
  fin_cases a <;> fin_cases d
  · change inner ℝ (B4a39 b i j) (B4a39 b i j) = 1
    exact F.e11
  · change inner ℝ (B4a39 b i j) (B4a40 b i j) = 0
    exact F.e12
  · change inner ℝ (B4a40 b i j) (B4a39 b i j) = 0
    rw [real_inner_comm]
    exact F.e12
  · change inner ℝ (B4a40 b i j) (B4a40 b i j) = 1
    exact F.e22
private theorem AS4B.B4a21 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a13 b i j 0 = B4a144 b i j := by
  have hr : B4a116 b i j ≠ 0 := ne_of_gt (B4a117 b i j)
  rw [B4a13,SphereGeom.circlePt,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,
    add_zero,B4a39,← mul_smul,mul_inv_cancel₀ hr,one_smul]
  abel
private theorem AS4B.B4a18 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    B4a13 b i j t ∈
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1 := by
  have hp : ∀ a : Fin 2,
      inner ℝ (b.c (B4a94 b i j)-b.c i) (![B4a39 b i j,B4a40 b i j] a) = 0 := by
    have F := B4a50 b i j
    have hdz : (dist (b.c i) (b.c (B4a94 b i j)))⁻¹ ≠ 0 :=
      inv_ne_zero (ne_of_gt (B4a38 b i j).1)
    intro a
    fin_cases a
    · have he := F.ae1
      simp only [B4a10,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
    · have he := F.ae2
      simp only [B4a10,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
  simpa only [B4a13,B4a89,B4a116,q,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons] using CircleArc.pair_circle_on_spheres
      (b.c i) (b.c (B4a94 b i j)) ![B4a39 b i j,B4a40 b i j]
      (B4a52 b i j) hp (B4a38 b i j).2 t
private theorem AS4B.B4a105 (b : B4a0) (i : Fin 4) (p : Pt)
    (hp : p ∈ patch b.c i) :
    dist (b.c i) (b.c (B4a94 b i 0))/2 ≤
      inner ℝ (B4a10 b i 0) (p-b.c i) := by
  have hball : p ∈ Metric.closedBall (b.c (B4a94 b i 0)) 1 := by
    have hk := hp.2
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
    exact hk _
  have hb := (CircleArc.ball_iff_inner (b.c i) (b.c (B4a94 b i 0)) p hp.1).mp hball
  have hd := (B4a38 b i 0).1
  have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
  have hl : (dist (b.c i) (b.c (B4a94 b i 0)))⁻¹ *
      (dist (b.c i) (b.c (B4a94 b i 0))^2/2) =
      dist (b.c i) (b.c (B4a94 b i 0))/2 := by field_simp
  rw [hl] at hm
  rw [B4a10,real_inner_smul_left,real_inner_comm]
  exact hm
private theorem AS4B.B4a106 (b : B4a0) (i : Fin 4) (p : Pt)
    (hp : p ∈ patch b.c i) : 0 < inner ℝ (B4a10 b i 0) (p-b.c i) :=
  lt_of_lt_of_le (half_pos (B4a38 b i 0).1)
    (B4a105 b i p hp)
private theorem AS4B.B4a111 (b : B4a0) (i : Fin 4) :
    ContinuousOn (B4a108 b i) (patch b.c i) := by
  intro p hp
  have hn : inner ℝ (B4a10 b i 0) (p-b.c i) ≠ 0 :=
    ne_of_gt (B4a106 b i p hp)
  apply ContinuousAt.continuousWithinAt
  unfold B4a108
  dsimp only
  fun_prop (disch := exact hn)
private theorem AS4B.B4a3 (b : B4a0) (i : Fin 4) : IsCompact (B4a1 b i) :=
  (B4a104 b.c i).image_of_continuousOn (B4a111 b i)
private theorem AS4B.B4a79 (b : B4a0) (i : Fin 4) (j : Fin 3) : 0 < B4a75 b i j := by
  let z : ℂ := ⟨inner ℝ (B4a39 b i j) (B4a42 b i j-B4a89 b i j),
    inner ℝ (B4a40 b i j) (B4a42 b i j-B4a89 b i j)⟩
  change 0 < (if 0 < Complex.arg z then Complex.arg z else Complex.arg z+2*Real.pi)
  split_ifs with h
  · exact h
  · have hg := Complex.neg_pi_lt_arg z
    linarith [Real.pi_pos]
private theorem AS4B.B4a76 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a75 b i j ≤ 2*Real.pi := by
  let z : ℂ := ⟨inner ℝ (B4a39 b i j) (B4a42 b i j-B4a89 b i j),
    inner ℝ (B4a40 b i j) (B4a42 b i j-B4a89 b i j)⟩
  change (if 0 < Complex.arg z then Complex.arg z else Complex.arg z+2*Real.pi) ≤ _
  split_ifs with h
  · have hg := Complex.arg_le_pi z
    linarith [Real.pi_pos]
  · linarith [le_of_not_gt h]
private theorem AS4B.B4a17 (m : SphereGeom.E3) (e : Fin 2 → SphereGeom.E3)
    (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b : ℝ)
    (hspan : b-a < 2*Real.pi) :
    Set.InjOn (SphereGeom.circlePt m (e 0) (e 1) r) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hm : max x y ≤ b := max_le hx.2 hy.2
  have hn : a ≤ min x y := le_min hx.1 hy.1
  have hs : max x y-min x y < 2*Real.pi := by linarith
  have heq := (CircleArc.intervalIntersection m e he r hr x x y y hs).1
  have hp : SphereGeom.circlePt m (e 0) (e 1) r x ∈
      (SphereGeom.circlePt m (e 0) (e 1) r '' Set.Icc x x) ∩
      (SphereGeom.circlePt m (e 0) (e 1) r '' Set.Icc y y) :=
    ⟨⟨x,⟨le_rfl,le_rfl⟩,rfl⟩,⟨y,⟨le_rfl,le_rfl⟩,hxy.symm⟩⟩
  rw [heq] at hp
  obtain ⟨t,ht,_⟩ := hp
  have hle : max x y ≤ min x y := ht.1.trans ht.2
  exact le_antisymm ((le_max_left _ _).trans (hle.trans (min_le_right _ _)))
    ((le_max_right _ _).trans (hle.trans (min_le_left _ _)))
private theorem AS4B.B4a20 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    B4a13 b i j t-b.c i =
      Gnomonic.capArc (B4a10 b i j) (B4a39 b i j) (B4a40 b i j)
        (dist (b.c i) (b.c (B4a94 b i j))/2) t := by
  let d : ℝ := dist (b.c i) (b.c (B4a94 b i j))
  have hd : d ≠ 0 := ne_of_gt (B4a38 b i j).1
  have hv : d • B4a10 b i j = b.c (B4a94 b i j)-b.c i := by
    change d • (d⁻¹ • (b.c (B4a94 b i j)-b.c i)) = _
    rw [← mul_smul,mul_inv_cancel₀ hd,one_smul]
  have hm : B4a89 b i j-b.c i = (d/2) • B4a10 b i j := by
    calc
      _ = (1/2 : ℝ) • (b.c (B4a94 b i j)-b.c i) := by unfold B4a89; module
      _ = (1/2 : ℝ) • (d • B4a10 b i j) := by rw [hv]
      _ = _ := by module
  have hr : B4a116 b i j = Real.sqrt (1-(d/2)^2) := by
    unfold B4a116 q
    congr 1
    dsimp [d]
    ring
  unfold B4a13 SphereGeom.circlePt Gnomonic.capArc
  change B4a89 b i j+B4a116 b i j •
    (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j)-b.c i = _
  rw [show B4a89 b i j+B4a116 b i j •
    (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j)-b.c i =
    (B4a89 b i j-b.c i)+B4a116 b i j •
    (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j) by abel,hm,hr]
private def AS4B.B4a147 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) : Pt :=
  Gnomonic.project (B4a10 b i 0) (B4a13 b i j t-b.c i)
end AS4Scope8
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope9
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2)
private theorem AS4B.B4a22 (f : E2 → ℝ)
    (hc : Continuous f) (hconc : ConcaveOn ℝ Set.univ f)
    (w : E2) (hw : 0 < f w) :
    interior {x : E2 | 0 ≤ f x} = {x : E2 | 0 < f x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    let δ : ℝ := ε/(2*(‖x-w‖+1))
    have hden : 0 < 2*(‖x-w‖+1) := by positivity
    have hδ : 0 < δ := div_pos hε hden
    have hdist : δ*‖x-w‖ < ε := by
      rw [show δ*‖x-w‖ = (ε*‖x-w‖)/(2*(‖x-w‖+1)) by dsimp [δ]; ring]
      apply (div_lt_iff₀ hden).mpr
      nlinarith [mul_nonneg hε.le (norm_nonneg (x-w))]
    let y : E2 := x+δ • (x-w)
    have hyball : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball,dist_eq_norm,
        show y-x = δ • (x-w) by dsimp [y]; abel,
        norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
      exact hdist
    have hy : 0 ≤ f y := hball hyball
    let α : ℝ := δ/(1+δ)
    let β : ℝ := 1/(1+δ)
    have hβ : 0 < β := by dsimp [β]; positivity
    have hα : 0 < α := by dsimp [α]; positivity
    have hαeq : α = δ*β := by dsimp [α,β]; ring
    have hβeq : (1+δ)*β = 1 := by dsimp [β]; field_simp
    have hab : α+β = 1 := by rw [hαeq]; nlinarith [hβeq]
    have hpoint : α • w+β • y = x := by
      rw [hαeq]
      calc
        _ = ((1+δ)*β) • x := by dsimp [y]; module
        _ = x := by rw [hβeq,one_smul]
    have hf := hconc.2 (Set.mem_univ w) (Set.mem_univ y) hα.le hβ.le hab
    rw [hpoint] at hf
    have hpos : 0 < α*f w+β*f y :=
      add_pos_of_pos_of_nonneg (mul_pos hα hw) (mul_nonneg hβ.le hy)
    exact lt_of_lt_of_le hpos hf
  · intro hx
    have hsub : {y : E2 | 0 < f y} ⊆ {y : E2 | 0 ≤ f y} := by
      intro y hy
      change 0 < f y at hy
      change 0 ≤ f y
      exact hy.le
    exact interior_maximal hsub (isOpen_lt continuous_const hc) hx
private theorem AS4B.B4a23 (f : Fin 3 → E2 → ℝ)
    (hc : ∀ j, Continuous (f j)) (hconc : ∀ j, ConcaveOn ℝ Set.univ (f j))
    (w : E2) (hw : ∀ j, 0 < f j w) :
    frontier {x : E2 | ∀ j, 0 ≤ f j x} =
      {x : E2 | (∀ j, 0 ≤ f j x) ∧ ∃ j, f j x = 0} := by
  let D : Set E2 := {x | ∀ j, 0 ≤ f j x}
  have hD : IsClosed D := by
    have he : D = ⋂ j, {x : E2 | 0 ≤ f j x} := by ext x; simp [D]
    rw [he]
    exact isClosed_iInter fun j => isClosed_le continuous_const (hc j)
  rw [hD.frontier_eq]
  ext x
  constructor
  · rintro ⟨hx,hn⟩
    refine ⟨hx,?_⟩
    by_contra hzero
    have hxstrict : ∀ j, 0 < f j x := by
      intro j
      have hne : f j x ≠ 0 := fun he => hzero ⟨j,he⟩
      exact lt_of_le_of_ne (hx j) hne.symm
    have hopen : IsOpen {y : E2 | ∀ j, 0 < f j y} := by
      have he : {y : E2 | ∀ j, 0 < f j y} = ⋂ j, {y : E2 | 0 < f j y} := by
        ext y; simp
      rw [he]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (hc j)
    have hsub : {y : E2 | ∀ j, 0 < f j y} ⊆ D := by
      intro y hy
      change ∀ j : Fin 3, 0 < f j y at hy
      change ∀ j : Fin 3, 0 ≤ f j y
      intro j
      exact (hy j).le
    exact hn (interior_maximal hsub hopen hxstrict)
  · rintro ⟨hx,⟨j,hj⟩⟩
    refine ⟨hx,?_⟩
    intro hi
    have hsub : D ⊆ {y : E2 | 0 ≤ f j y} := by
      intro y hy
      change ∀ k : Fin 3, 0 ≤ f k y at hy
      exact hy j
    have hij : x ∈ interior {y : E2 | 0 ≤ f j y} := interior_mono hsub hi
    rw [B4a22 (f j) (hc j) (hconc j) w (hw j)] at hij
    change 0 < f j x at hij
    linarith
private theorem AS4B.B4a31 (n v u w : Pt) (A B C D : ℝ) :
    inner ℝ n (SphereGeom.cross (A • v+B • u) (C • w+D • u)) =
      A*C*inner ℝ n (SphereGeom.cross v w)+A*D*inner ℝ n (SphereGeom.cross v u)+
        B*C*inner ℝ n (SphereGeom.cross u w)+B*D*inner ℝ n (SphereGeom.cross u u) := by
  simp only [AS4T.inner_coords,AS4T.cross_coords]
  simp
  ring
private theorem AS4B.B4a33 (n a u w : Pt) :
    inner ℝ n (SphereGeom.cross (SphereGeom.cross a u) w) =
      inner ℝ n u*inner ℝ a w-inner ℝ n a*inner ℝ u w := by
  simp only [AS4T.inner_coords,AS4T.cross_coords]
  simp
  ring
private theorem AS4B.B4a30 (n a u w : Pt) :
    (inner ℝ n u)^2*inner ℝ a w-
      inner ℝ n u*inner ℝ n a*inner ℝ u w-
      inner ℝ n u*inner ℝ n w*inner ℝ a u+
      inner ℝ n w*inner ℝ n a*inner ℝ u u-
      inner ℝ n (SphereGeom.cross a u)*inner ℝ n (SphereGeom.cross u w) =
    inner ℝ n n*(inner ℝ u u*inner ℝ a w-inner ℝ a u*inner ℝ u w) := by
  simp only [AS4T.inner_coords,AS4T.cross_coords]
  simp
  ring
private theorem AS4B.B4a115 (n a u w : Pt) (h : ℝ)
    (hn : inner ℝ n n = 1) (hu : inner ℝ u u = 1) (hw : inner ℝ w w = 1)
    (hh : 0 ≤ h) (hboundary : inner ℝ a u = h) (hcap : h ≤ inner ℝ a w)
    (hnu : 0 < inner ℝ n u) (hnw : 0 < inner ℝ n w) :
    0 ≤ inner ℝ n (SphereGeom.cross (Gnomonic.projectVelocity n u (SphereGeom.cross a u))
      (Gnomonic.project n w-Gnomonic.project n u)) := by
  let q := inner ℝ n u
  let p := inner ℝ n w
  let v := SphereGeom.cross a u
  have hqu : inner ℝ u n = q := real_inner_comm n u
  have hpw : inner ℝ w n = p := real_inner_comm n w
  have hvn : inner ℝ v n = inner ℝ n v := real_inner_comm n v
  have hq : q ≠ 0 := ne_of_gt hnu
  have hp : p ≠ 0 := ne_of_gt hnw
  have hdiff : Gnomonic.project n w-Gnomonic.project n u =
      p⁻¹ • w+(-q⁻¹) • u := by
    unfold Gnomonic.project
    rw [hqu,hpw]
    module
  have hself : inner ℝ n (SphereGeom.cross u u) = 0 := by
    simp only [AS4T.inner_coords,AS4T.cross_coords]
    simp
    ring
  have hid : inner ℝ n (SphereGeom.cross (Gnomonic.projectVelocity n u (SphereGeom.cross a u))
      (Gnomonic.project n w-Gnomonic.project n u)) =
      (inner ℝ a w-h*inner ℝ u w)/(q^2*p) := by
    have hpoly := B4a30 n a u w
    rw [hn,hu,hboundary] at hpoly
    change q^2*inner ℝ a w-q*inner ℝ n a*inner ℝ u w-
      q*p*h+p*inner ℝ n a*1-inner ℝ n v*inner ℝ n (SphereGeom.cross u w) =
      1*(1*inner ℝ a w-h*inner ℝ u w) at hpoly
    calc
      _ = (q^2*inner ℝ a w-q*inner ℝ n a*inner ℝ u w-
          q*p*h+p*inner ℝ n a-inner ℝ n v*inner ℝ n (SphereGeom.cross u w))/(q^2*p) := by
        rw [hdiff,Gnomonic.projectVelocity,hqu,hvn,B4a31,hself]
        rw [B4a33,B4a33,hu,hboundary]
        change q⁻¹*p⁻¹*(q*inner ℝ a w-inner ℝ n a*inner ℝ u w)+
          q⁻¹*(-q⁻¹)*(q*h-inner ℝ n a*1)+
          (-inner ℝ n v/q^2)*p⁻¹*inner ℝ n (SphereGeom.cross u w)+
          (-inner ℝ n v/q^2)*(-q⁻¹)*0 = _
        field_simp [hq,hp] <;> ring
      _ = _ := by congr 1; simpa only [mul_one,one_mul] using hpoly
  have hdot : inner ℝ u w ≤ 1 := by
    have hwu : inner ℝ w u = inner ℝ u w := real_inner_comm u w
    have hnorm : 0 ≤ inner ℝ (u-w) (u-w) := by rw [real_inner_self_eq_norm_sq]; positivity
    simp only [inner_sub_left,inner_sub_right,hu,hw,hwu] at hnorm
    linarith
  rw [hid]
  have hl : h*inner ℝ u w ≤ h := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdot hh
  exact div_nonneg (sub_nonneg.mpr (hl.trans hcap)) (mul_nonneg (sq_nonneg q) hnw.le)
end AS4Scope9
noncomputable section
open scoped Topology ContDiff
section AS4Scope10
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4P
private def AS4P.smoothReciprocalDenom (δ t : ℝ) : ℝ :=
  δ / 2 + (t - δ / 2) * Real.smoothTransition ((t - δ / 2) / (δ / 2))
private def AS4P.smoothReciprocalExtension (δ t : ℝ) : ℝ :=
  (smoothReciprocalDenom δ t)⁻¹
private theorem AS4P.smoothReciprocalDenom_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 < smoothReciprocalDenom δ t := by
  have hδ2 : 0 < δ / 2 := by positivity
  by_cases ht : t ≤ δ / 2
  · have harg : (t - δ / 2) / (δ / 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ2.le
    simp only [smoothReciprocalDenom, Real.smoothTransition.zero_of_nonpos harg,
      mul_zero, add_zero]
    exact hδ2
  · unfold smoothReciprocalDenom
    exact add_pos_of_pos_of_nonneg hδ2
      (mul_nonneg (by linarith) (Real.smoothTransition.nonneg _))
@[fun_prop]
private theorem AS4P.smoothReciprocalDenom_contDiff (δ : ℝ) :
    ContDiff ℝ ∞ (smoothReciprocalDenom δ) := by
  unfold smoothReciprocalDenom
  fun_prop
@[fun_prop]
private theorem AS4P.smoothReciprocalExtension_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothReciprocalExtension δ) := by
  exact (smoothReciprocalDenom_contDiff δ).inv
    (fun t => (smoothReciprocalDenom_pos δ hδ t).ne')
private theorem AS4P.smoothReciprocalDenom_eq (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : δ ≤ t) :
    smoothReciprocalDenom δ t = t := by
  have hδ2 : 0 < δ / 2 := by positivity
  have harg : 1 ≤ (t - δ / 2) / (δ / 2) :=
    (one_le_div hδ2).mpr (by linarith)
  simp only [smoothReciprocalDenom, Real.smoothTransition.one_of_one_le harg, mul_one]
  ring
private theorem AS4P.smoothReciprocalExtension_eq (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : δ ≤ t) :
    smoothReciprocalExtension δ t = 1 / t := by
  simp only [smoothReciprocalExtension, smoothReciprocalDenom_eq δ hδ t ht, one_div]
section Candidate
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
private def AS4P.rawCircleCandidate (h ρ : ℝ) (e e1 e2 : E) (t : ℝ) : E :=
  h • e + ρ • (Real.cos t • e1 + Real.sin t • e2)
@[fun_prop]
private theorem AS4P.rawCircleCandidate_contDiff (h ρ : ℝ) (e e1 e2 : E) :
    ContDiff ℝ ∞ (rawCircleCandidate h ρ e e1 e2) := by
  unfold rawCircleCandidate
  fun_prop
private def AS4P.extendedGnomonicArc (δ h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) (t : ℝ) : H :=
  L (smoothReciprocalExtension δ (inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) •
    rawCircleCandidate h ρ e e1 e2 t - n)
private def AS4P.gnomonicArcCandidate (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) (t : ℝ) : H :=
  L ((1 / inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) •
    rawCircleCandidate h ρ e e1 e2 t - n)
@[fun_prop]
private theorem AS4P.extendedGnomonicArc_contDiff (δ : ℝ) (hδ : 0 < δ)
    (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) :
    ContDiff ℝ ∞ (extendedGnomonicArc δ h ρ e e1 e2 n L) := by
  have hu := rawCircleCandidate_contDiff h ρ e e1 e2
  have hd : ContDiff ℝ ∞ (fun t => inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) :=
    contDiff_const.inner ℝ hu
  have hF := (smoothReciprocalExtension_contDiff δ hδ).comp hd
  exact L.contDiff.comp ((hF.smul hu).sub contDiff_const)
private theorem AS4P.extendedGnomonicArc_contDiff_two (δ : ℝ) (hδ : 0 < δ)
    (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) :
    ContDiff ℝ 2 (extendedGnomonicArc δ h ρ e e1 e2 n L) := by
  exact contDiff_infty.mp (extendedGnomonicArc_contDiff δ hδ h ρ e e1 e2 n L) 2
private theorem AS4P.extendedGnomonicArc_eq (δ : ℝ) (hδ : 0 < δ)
    (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) (t : ℝ)
    (ht : δ ≤ inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) :
    extendedGnomonicArc δ h ρ e e1 e2 n L t =
      gnomonicArcCandidate h ρ e e1 e2 n L t := by
  unfold extendedGnomonicArc gnomonicArcCandidate
  rw [smoothReciprocalExtension_eq δ hδ _ ht]
end Candidate
end AS4Scope10
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope11
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2)
private def AS4B.B4a24 (b : B4a0) (i : Fin 4) : Pt →L[ℝ] E2 where
  toFun u := WithLp.toLp 2 ![inner ℝ (B4a39 b i 0) u,inner ℝ (B4a40 b i 0) u]
  map_add' u v := by ext j; fin_cases j <;> simp [inner_add_right]
  map_smul' a u := by ext j; fin_cases j <;> simp [real_inner_smul_right]
  cont := by fun_prop
private theorem AS4B.B4a28 (b : B4a0) (i : Fin 4) (p : Pt) :
    B4a24 b i (Gnomonic.project (B4a10 b i 0) (p-b.c i)) =
      B4a108 b i p := by
  have F := B4a50 b i 0
  have he0 : inner ℝ (B4a39 b i 0) (B4a10 b i 0) = 0 :=
    (real_inner_comm (B4a10 b i 0) (B4a39 b i 0)).trans F.ae1
  have he1 : inner ℝ (B4a40 b i 0) (B4a10 b i 0) = 0 :=
    (real_inner_comm (B4a10 b i 0) (B4a40 b i 0)).trans F.ae2
  have hh : inner ℝ (p-b.c i) (B4a10 b i 0) =
      inner ℝ (B4a10 b i 0) (p-b.c i) := real_inner_comm (B4a10 b i 0) (p-b.c i)
  ext j
  fin_cases j <;>
    simp [B4a24,Gnomonic.project,B4a108,inner_sub_right,
      real_inner_smul_right,he0,he1,hh,div_eq_mul_inv,mul_comm]
private def AS4B.B4a63 (b : B4a0) (i : Fin 4) (j : Fin 3) : ℝ :=
  dist (b.c i) (b.c (B4a94 b i j))/2
private def AS4B.B4a46 (b : B4a0) (i : Fin 4) : ℝ :=
  dist (b.c i) (b.c (B4a94 b i 0))/4
private theorem AS4B.B4a47 (b : B4a0) (i : Fin 4) : 0 < B4a46 b i :=
  div_pos (B4a38 b i 0).1 (by norm_num)
private theorem AS4B.B4a118 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    rawCircleCandidate (B4a63 b i j) (B4a116 b i j)
      (B4a10 b i j) (B4a39 b i j) (B4a40 b i j) t = B4a13 b i j t-b.c i := by
  have hr : B4a116 b i j = Real.sqrt (1-(B4a63 b i j)^2) := by
    unfold B4a116 B4a63 q
    congr 1
    ring
  rw [hr]
  change Gnomonic.capArc (B4a10 b i j) (B4a39 b i j) (B4a40 b i j) (B4a63 b i j) t = _
  exact (B4a20 b i j t).symm
private def AS4B.B4a55 (b : B4a0) (i : Fin 4) (j : Fin 3) : ℝ → E2 :=
  extendedGnomonicArc (B4a46 b i) (B4a63 b i j) (B4a116 b i j)
    (B4a10 b i j) (B4a39 b i j) (B4a40 b i j) (B4a10 b i 0) (B4a24 b i)
private theorem AS4B.B4a56 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ContDiff ℝ 2 (B4a55 b i j) :=
  extendedGnomonicArc_contDiff_two _ (B4a47 b i) _ _ _ _ _ _ _
private theorem AS4B.B4a58 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (hm : B4a46 b i ≤ inner ℝ (B4a10 b i 0) (B4a13 b i j t-b.c i)) :
    B4a55 b i j t = B4a54 b i j t := by
  have hraw := B4a118 b i j t
  have he := extendedGnomonicArc_eq (B4a46 b i) (B4a47 b i)
    (B4a63 b i j) (B4a116 b i j) (B4a10 b i j) (B4a39 b i j) (B4a40 b i j)
    (B4a10 b i 0) (B4a24 b i) t (by simpa only [hraw] using hm)
  change extendedGnomonicArc _ _ _ _ _ _ _ _ t = _
  rw [he]
  calc
    _ = B4a24 b i (Gnomonic.project (B4a10 b i 0) (B4a13 b i j t-b.c i)) := by
      unfold gnomonicArcCandidate
      rw [hraw]
      congr 1
      unfold Gnomonic.project
      rw [one_div,real_inner_comm]
    _ = _ := B4a28 b i (B4a13 b i j t)
private theorem AS4B.B4a59 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (hp : B4a13 b i j t ∈ patch b.c i) :
    B4a55 b i j t = B4a54 b i j t := by
  apply B4a58
  have hl := B4a105 b i (B4a13 b i j t) hp
  have hd := (B4a38 b i 0).1
  unfold B4a46
  linarith
end AS4Scope11
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope12
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 cross2)
private def AS4B.B4a138 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Pt) (y : E2) : ℝ :=
  inner ℝ v (n+L y)-(‖v‖^2/2)*‖n+L y‖
private theorem AS4B.B4a140 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Pt) :
    Continuous (B4a138 n L v) := by
  unfold B4a138
  fun_prop
private theorem AS4B.B4a139 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Pt) :
    ConcaveOn ℝ Set.univ (B4a138 n L v) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have hs : a • n+b • n = n := by rw [← add_smul,hab,one_smul]
  have hvec : n+L (a • x+b • y) = a • (n+L x)+b • (n+L y) := by
    calc
      _ = n+(a • L x+b • L y) := by simp only [map_add,map_smul]
      _ = (a • n+b • n)+(a • L x+b • L y) := by rw [hs]
      _ = _ := by module
  have hnorm := norm_add_le (a • (n+L x)) (b • (n+L y))
  simp only [norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb] at hnorm
  have hn := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ ‖v‖^2/2 by positivity)
  change a*B4a138 n L v x+b*B4a138 n L v y ≤
    B4a138 n L v (a • x+b • y)
  unfold B4a138
  rw [hvec]
  simp only [inner_add_right,real_inner_smul_right]
  nlinarith [hn]
private theorem AS4B.B4a143 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Fin 3 → Pt)
    (w : E2) (hw : ∀ j, 0 < B4a138 n L (v j) w) :
    frontier {y : E2 | ∀ j, (‖v j‖^2/2)*‖n+L y‖ ≤ inner ℝ (v j) (n+L y)} =
      {y : E2 | (∀ j, (‖v j‖^2/2)*‖n+L y‖ ≤ inner ℝ (v j) (n+L y)) ∧
        ∃ j, (‖v j‖^2/2)*‖n+L y‖ = inner ℝ (v j) (n+L y)} := by
  have h := B4a23 (fun j => B4a138 n L (v j))
    (fun j => B4a140 n L (v j))
    (fun j => B4a139 n L (v j)) w hw
  have hD : {y : E2 | ∀ j, (‖v j‖^2/2)*‖n+L y‖ ≤ inner ℝ (v j) (n+L y)} =
      {y : E2 | ∀ j, 0 ≤ B4a138 n L (v j) y} := by
    ext y
    simp only [Set.mem_setOf_eq,B4a138,sub_nonneg]
  rw [hD,h]
  ext y
  constructor
  · rintro ⟨hy,⟨j,hj⟩⟩
    refine ⟨?_,j,?_⟩
    · simpa only [B4a138,sub_nonneg] using hy
    · exact (sub_eq_zero.mp hj).symm
  · rintro ⟨hy,⟨j,hj⟩⟩
    refine ⟨?_,j,?_⟩
    · simpa only [B4a138,sub_nonneg] using hy
    · exact sub_eq_zero.mpr hj.symm
private theorem AS4B.B4a25 (e n v w : Pt) :
    inner ℝ e v*inner ℝ (SphereGeom.cross n e) w-inner ℝ (SphereGeom.cross n e) v*inner ℝ e w =
      inner ℝ e e*inner ℝ n (SphereGeom.cross v w)-inner ℝ n e*inner ℝ e (SphereGeom.cross v w) := by
  simp only [AS4T.inner_coords,AS4T.cross_coords]
  simp
  ring
private theorem AS4B.B4a27 (b : B4a0) (i : Fin 4) (v w : Pt) :
    cross2 (B4a24 b i v) (B4a24 b i w) =
      inner ℝ (B4a10 b i 0) (SphereGeom.cross v w) := by
  have F := B4a50 b i 0
  have h := B4a25 (B4a39 b i 0) (B4a10 b i 0) v w
  rw [F.e11,F.ae1] at h
  change inner ℝ (B4a39 b i 0) v*inner ℝ (B4a40 b i 0) w-
    inner ℝ (B4a40 b i 0) v*inner ℝ (B4a39 b i 0) w = _
  simpa only [B4a40,one_mul,zero_mul,sub_zero] using h
private theorem AS4B.B4a29 (b : B4a0) (i : Fin 4)
    (a u w : Pt) (h : ℝ) (hu : inner ℝ u u = 1) (hw : inner ℝ w w = 1)
    (hh : 0 ≤ h) (hboundary : inner ℝ a u = h) (hcap : h ≤ inner ℝ a w)
    (hnu : 0 < inner ℝ (B4a10 b i 0) u) (hnw : 0 < inner ℝ (B4a10 b i 0) w) :
    0 ≤ cross2
      (B4a24 b i (Gnomonic.projectVelocity (B4a10 b i 0) u (SphereGeom.cross a u)))
      (B4a24 b i (Gnomonic.project (B4a10 b i 0) w-Gnomonic.project (B4a10 b i 0) u)) := by
  rw [B4a27]
  exact B4a115 _ a u w h (B4a50 b i 0).aa hu hw hh hboundary hcap hnu hnw
private theorem AS4B.B4a36 (a u v : Pt) (A B : ℝ) :
    SphereGeom.cross a (A • u+B • v) = A • SphereGeom.cross a u+B • SphereGeom.cross a v := by
  ext j
  fin_cases j <;> simp [AS4T.cross_coords] <;> ring
private theorem AS4B.B4a37 (a : Pt) : SphereGeom.cross a a = 0 := by
  ext j
  fin_cases j <;> simp [AS4T.cross_coords] <;> ring
private theorem AS4B.B4a34 (a e : Pt) :
    SphereGeom.cross a (SphereGeom.cross a e) = inner ℝ a e • a-inner ℝ a a • e := by
  simp only [AS4T.cross_coords,AS4T.inner_coords]
  ext j
  fin_cases j <;> simp <;> ring
private theorem AS4B.B4a12 (a e : Pt) (h t : ℝ)
    (haa : inner ℝ a a = 1) (hae : inner ℝ a e = 0) :
    Gnomonic.capVelocity e (SphereGeom.cross a e) h t =
      SphereGeom.cross a (Gnomonic.capArc a e (SphereGeom.cross a e) h t) := by
  have he : SphereGeom.cross a (SphereGeom.cross a e) = -e := by
    rw [B4a34,hae,haa,zero_smul,one_smul,zero_sub]
  unfold Gnomonic.capVelocity Gnomonic.capArc
  rw [B4a36,B4a37,smul_zero,zero_add]
  have hlinear : SphereGeom.cross a (Real.cos t • e+Real.sin t • SphereGeom.cross a e) =
      Real.cos t • SphereGeom.cross a e+Real.sin t • (-e) := by rw [B4a36,he]
  rw [hlinear]
  module
end AS4Scope12
noncomputable section
open SphereGeom
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
section AS4Scope13
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
end AS4Scope13
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope14
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
private def AS4B.B4a41 (b : B4a0) (i : Fin 4) (j : Fin 3) : ℂ :=
  ⟨inner ℝ (B4a39 b i j) (B4a42 b i j-B4a89 b i j),
   inner ℝ (B4a40 b i j) (B4a42 b i j-B4a89 b i j)⟩
private theorem AS4B.B4a44 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ∃ t ∈ Set.Icc (0 : ℝ) (2*Real.pi), B4a13 b i j t = B4a42 b i j := by
  have hp : ∀ a : Fin 2,
      inner ℝ (b.c (B4a94 b i j)-b.c i) (![B4a39 b i j,B4a40 b i j] a) = 0 := by
    have F := B4a50 b i j
    have hdz : (dist (b.c i) (b.c (B4a94 b i j)))⁻¹ ≠ 0 :=
      inv_ne_zero (ne_of_gt (B4a38 b i j).1)
    intro a
    fin_cases a
    · have he := F.ae1
      simp only [B4a10,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
    · have he := F.ae2
      simp only [B4a10,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
  have hchart := CircleArc.pair_sphere_chart_two
    (b.c i) (b.c (B4a94 b i j)) ![B4a39 b i j,B4a40 b i j]
    (B4a52 b i j) hp (B4a38 b i j).1 (B4a38 b i j).2
  have hmem := B4a45 b i j
  rw [hchart] at hmem
  simpa only [B4a13,B4a89,B4a116,q,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Set.mem_image] using hmem
private theorem AS4B.B4a43 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ‖B4a41 b i j‖ = B4a116 b i j ∧
    B4a42 b i j = B4a89 b i j +
      (B4a41 b i j).re • B4a39 b i j +
      (B4a41 b i j).im • B4a40 b i j := by
  obtain ⟨t,ht,he⟩ := B4a44 b i j
  have F := B4a50 b i j
  have h01 : inner ℝ (B4a40 b i j) (B4a39 b i j) = 0 := by
    rw [real_inner_comm]; exact F.e12
  have hvec : B4a42 b i j-B4a89 b i j =
      (B4a116 b i j*Real.cos t) • B4a39 b i j +
      (B4a116 b i j*Real.sin t) • B4a40 b i j := by
    rw [← he,B4a13,SphereGeom.circlePt]
    simp only [smul_add,smul_smul]
    abel
  have hre : (B4a41 b i j).re = B4a116 b i j*Real.cos t := by
    change inner ℝ (B4a39 b i j) (B4a42 b i j-B4a89 b i j) = _
    rw [hvec]
    simp only [inner_add_right,real_inner_smul_right,
      F.e11,F.e12,mul_one,mul_zero,add_zero]
  have him : (B4a41 b i j).im = B4a116 b i j*Real.sin t := by
    change inner ℝ (B4a40 b i j) (B4a42 b i j-B4a89 b i j) = _
    rw [hvec]
    simp only [inner_add_right,real_inner_smul_right,
      F.e22,h01,mul_one,mul_zero,zero_add]
  have hn : ‖B4a41 b i j‖^2 = (B4a116 b i j)^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,hre,him]
    nlinarith [Real.sin_sq_add_cos_sq t]
  constructor
  · nlinarith [norm_nonneg (B4a41 b i j),(B4a117 b i j)]
  · rw [hre,him,← he,B4a13,SphereGeom.circlePt]
    simp only [smul_add,smul_smul]
    abel
private theorem AS4B.B4a16 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a13 b i j (B4a75 b i j) = B4a42 b i j := by
  have H := B4a43 b i j
  have hc : B4a116 b i j*Real.cos (B4a75 b i j) = (B4a41 b i j).re := by
    have hh := Complex.norm_mul_cos_arg (B4a41 b i j)
    rw [H.1] at hh
    change B4a116 b i j*Real.cos
      (if 0 < (B4a41 b i j).arg then (B4a41 b i j).arg
        else (B4a41 b i j).arg+2*Real.pi) = _
    split_ifs <;> simpa only [Real.cos_add_two_pi] using hh
  have hs : B4a116 b i j*Real.sin (B4a75 b i j) = (B4a41 b i j).im := by
    have hh := Complex.norm_mul_sin_arg (B4a41 b i j)
    rw [H.1] at hh
    change B4a116 b i j*Real.sin
      (if 0 < (B4a41 b i j).arg then (B4a41 b i j).arg
        else (B4a41 b i j).arg+2*Real.pi) = _
    split_ifs <;> simpa only [Real.sin_add_two_pi] using hh
  rw [B4a13,SphereGeom.circlePt]
  simp only [smul_add,smul_smul,hc,hs]
  simpa only [add_assoc] using H.2.symm
private theorem AS4B.B4a15 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a13 b i j (B4a75 b i j) = B4a13 b i (j+1) 0 := by
  rw [B4a16,B4a21,B4a151]
private theorem AS4B.B4a78 (b : B4a0) (i : Fin 4) (j : Fin 3)
    (hne : B4a144 b i j ≠ B4a42 b i j) :
    B4a75 b i j < 2*Real.pi := by
  have hh := B4a76 b i j
  apply lt_of_le_of_ne hh
  intro he
  apply hne
  have hc := B4a16 b i j
  rw [he,B4a13,SphereGeom.circlePt,Real.cos_two_pi,Real.sin_two_pi,
    one_smul,zero_smul,add_zero] at hc
  have h0 := B4a21 b i j
  rw [B4a13,SphereGeom.circlePt,Real.cos_zero,Real.sin_zero,
    one_smul,zero_smul,add_zero] at h0
  exact h0.symm.trans hc
private theorem AS4B.B4a93 (B : B4a0) (x : Pt)
    (hx : ∀ m : Fin 4, dist x (B.c m) = 1) : False := by
  let c := B.c
  let X := B.X
  let Y := B.Y
  let s := B.s
  let l : Fin 4 := 0
  have hc : IsPathConfig c X Y s := B.path
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  let v := c j-c i
  let w := c k-c i
  let z := c l-c i
  let D := AS4T.faceDelta v w
  let Q := AS4T.faceQ v w
  let N := AS4T.orientedNormal v w z
  let h := AS4T.height v w
  let o := AS4T.center v w
  let p := c i + (o+h•N)
  let m := c i + (o-h•N)
  let a := AS4T.sq z - 2*inner ℝ z o
  let b := 2*h*inner ℝ z N
  have hDP : D = Dpoly X Y s l := (face_TG_D c l).trans (face_polys c X Y s hc l).2.1
  have hQP : Q = Qpoly X Y s l := (face_TG_Q c l).trans (face_polys c X Y s hc l).1
  have hD : 0 < D := by rw [hDP]; exact path_Dpoly_pos c X Y s hc l
  have hQ : 0 < Q := by rw [hQP]; exact path_Qpoly_pos c X Y s hc l
  have hQface : 0 < Qface c l := by rw [← face_TG_Q c l]; exact hQ
  have hdet : 4*(inner ℝ z (SphereGeom.cross v w))^2 = Hpoly X Y s := by
    have hg := gram_from_q c i j k l
    rw [(face_polys c X Y s hc l).2.2.2] at hg
    simpa only [real_inner_comm] using hg
  have hG : inner ℝ z (SphereGeom.cross v w) ≠ 0 := by intro hz; rw [hz] at hdet; nlinarith [hc.H_pos]
  have hn : 0 < inner ℝ z N := AS4T.normal_oriented v w z hD hG
  have hh : 0 < h := AS4T.height_pos v w hD hQ
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hh) hn
  have hpm : p ≠ m := by
    exact fun he => AS4T.triple_points_ne v w z hD hQ (add_left_cancel he)
  have htr : triplePts c l = {p,m} := by
    rw [triplePts_translate c l]
    change {x | x-c i ∈ AS4T.triple v w} = {p,m}
    rw [AS4T.triple_exact v w z hD hQ]
    ext x
    simp [p,m,o,h,N,Set.mem_insert_iff,Set.mem_singleton_iff,sub_eq_iff_eq_add,add_comm]
  have hp : (dist p (c l))^2-1 = a-b := by
    have he : p-c l = o+h•N-z := by dsimp [p,z]; abel
    rw [dist_eq_norm,he]
    exact AS4T.fourth_sq_formula v w z h hD hQ rfl
  have hm : (dist m (c l))^2-1 = a+b := by
    have he : m-c l = o+(-h)•N-z := by dsimp [m,z]; simp only [neg_smul]; abel
    rw [dist_eq_norm,he,AS4T.fourth_sq_formula v w z (-h) hD hQ (neg_sq h)]
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
  have hneg : a^2-b^2 < 0 := by
    have hid : D^2*(a^2-b^2) = -D*P4poly X Y s := by
      calc D^2*(a^2-b^2) = (D*a)^2-D^2*b^2 := by ring
           _ = Apoly X Y s l^2-4*Hpoly X Y s*Qpoly X Y s l := by rw [ha,hb2]
           _ = -D*P4poly X Y s := hdisc
    have hprod : D^2*(a^2-b^2) < 0 := by
      rw [hid]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hD) B.bulk
    by_contra! hh
    have hm : 0 ≤ D^2*(a^2-b^2) := mul_nonneg (sq_nonneg _) hh
    linarith only [hprod,hm]
  have hmem : x ∈ triplePts c l := by
    change ∀ m, m ≠ l → dist x (c m) = 1
    exact fun m _ => hx m
  rw [htr] at hmem
  have hx4 : (dist x (c l))^2-1 = 0 := by rw [hx l]; norm_num
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hmem
  rcases hmem with hxp | hxm
  · rw [hxp,hp] at hx4
    have hab : a = b := sub_eq_zero.mp hx4
    rw [hab,sub_self] at hneg
    exact lt_irrefl _ hneg
  · rw [hxm,hm] at hx4
    have hab : a = -b := by linarith only [hx4]
    rw [hab,neg_sq,sub_self] at hneg
    exact lt_irrefl _ hneg
private theorem AS4B.B4a152 (b : B4a0) : Function.Injective (B4a150 b) := by
  intro l k he
  by_contra hne
  apply B4a93 b (B4a150 b l)
  intro m
  by_cases hml : m = l
  · subst m
    have hk := (B4a153 b k).1
    change ∀ a, a ≠ k → dist (B4a150 b k) (b.c a) = 1 at hk
    rw [he]
    exact hk l hne
  · have hl := (B4a153 b l).1
    change ∀ a, a ≠ l → dist (B4a150 b l) (b.c a) = 1 at hl
    exact hl m hml
private theorem AS4B.B4a145 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a144 b i j ≠ B4a42 b i j := by
  intro he
  have ho := B4a152 b he
  exact B4a92 (j+1) (B4a96 b i ho)
private theorem AS4B.B4a77 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a75 b i j < 2*Real.pi :=
  B4a78 b i j (B4a145 b i j)
end AS4Scope14
noncomputable section
open Real SphereGeom
section AS4Scope15
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4S
private abbrev AS4S.E2 := EuclideanSpace ℝ (Fin 2)
private theorem AS4S.norm_affine_region_convex {ι : Type*} (n : E3) (L : E2 →ₗ[ℝ] E3) (v : ι → E3) :
    Convex ℝ {y : E2 | ∀ j, (‖v j‖^2/2)*‖n+L y‖ ≤ inner ℝ (v j) (n+L y)} := by
  intro x hx y hy a b ha hb hab
  change ∀ j, (‖v j‖^2/2)*‖n+L (a • x + b • y)‖ ≤ inner ℝ (v j) (n+L (a • x + b • y))
  intro j
  have hs : a • n + b • n = n := by rw [←add_smul,hab,one_smul]
  have hvec : n+L (a • x + b • y) = a • (n+L x) + b • (n+L y) := by
    calc
      n+L (a • x + b • y) = n+(a • L x + b • L y) := by simp only [map_add,map_smul]
      _ = (a • n+b • n)+(a • L x+b • L y) := by rw [hs]
      _ = a • (n+L x)+b • (n+L y) := by module
  have hnorm := norm_add_le (a • (n+L x)) (b • (n+L y))
  simp only [norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb] at hnorm
  have hr : 0 ≤ ‖v j‖^2/2 := div_nonneg (sq_nonneg _) (by norm_num)
  have hn := mul_le_mul_of_nonneg_left hnorm hr
  have hax := mul_le_mul_of_nonneg_left (hx j) ha
  have hby := mul_le_mul_of_nonneg_left (hy j) hb
  rw [hvec]
  calc
    (‖v j‖^2/2)*‖a • (n+L x)+b • (n+L y)‖ ≤
        (‖v j‖^2/2)*(a*‖n+L x‖+b*‖n+L y‖) := hn
    _ = a*((‖v j‖^2/2)*‖n+L x‖)+b*((‖v j‖^2/2)*‖n+L y‖) := by ring
    _ ≤ a*inner ℝ (v j) (n+L x)+b*inner ℝ (v j) (n+L y) := add_le_add hax hby
    _ = inner ℝ (v j) (a • (n+L x)+b • (n+L y)) := by
      simp only [inner_add_right,inner_smul_right]
private theorem AS4S.unit_ball_iff_norm_affine (n u v : E3) (L : E2 →ₗ[ℝ] E3) (y : E2)
    (t : ℝ) (hu : ‖u‖ = 1) (ht : 0 < t) (hrep : n+L y = t⁻¹ • u) :
    dist u v ≤ 1 ↔ (‖v‖^2/2)*‖n+L y‖ ≤ inner ℝ v (n+L y) := by
  have hd : dist u v ^ 2 = 1 - 2 * inner ℝ v u + ‖v‖^2 := by
    rw [dist_eq_norm,norm_sub_sq_real,hu,real_inner_comm v u]
    ring
  have hb : dist u v ≤ 1 ↔ ‖v‖^2/2 ≤ inner ℝ v u := by
    constructor
    · intro h; nlinarith [dist_nonneg (x:=u) (y:=v)]
    · intro h; nlinarith [dist_nonneg (x:=u) (y:=v)]
  rw [hb,hrep,norm_smul,inner_smul_right,Real.norm_of_nonneg (inv_nonneg.mpr ht.le),hu,mul_one]
  constructor
  · intro h
    calc
      (‖v‖^2/2)*t⁻¹ ≤ (inner ℝ v u)*t⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr ht.le)
      _ = t⁻¹*inner ℝ v u := mul_comm _ _
  · intro h
    have hh := mul_le_mul_of_nonneg_right h ht.le
    calc
      ‖v‖^2/2 = ((‖v‖^2/2)*t⁻¹)*t := by field_simp [ht.ne']
      _ ≤ (t⁻¹*inner ℝ v u)*t := hh
      _ = inner ℝ v u := by field_simp [ht.ne']
end AS4Scope15
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope16
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2)
private theorem AS4B.full_frame_on (a e f : Pt) (F : Gnomonic.CapFrame a e f) :
    Orthonormal ℝ ![e,f,a] := by
  apply orthonormal_iff_ite.mpr
  intro j k
  fin_cases j <;> fin_cases k
  · change inner ℝ e e = 1; exact F.e11
  · change inner ℝ e f = 0; exact F.e12
  · change inner ℝ e a = 0; rw [real_inner_comm];exact F.ae1
  · change inner ℝ f e = 0; rw [real_inner_comm];exact F.e12
  · change inner ℝ f f = 1; exact F.e22
  · change inner ℝ f a = 0; rw [real_inner_comm];exact F.ae2
  · change inner ℝ a e = 0; exact F.ae1
  · change inner ℝ a f = 0; exact F.ae2
  · change inner ℝ a a = 1; exact F.aa
private def AS4B.B4a53 (b : B4a0) (i : Fin 4) : OrthonormalBasis (Fin 3) ℝ Pt :=
  OrthonormalBasis.mk (full_frame_on _ _ _ (B4a50 b i 0))
    ((full_frame_on _ _ _ (B4a50 b i 0)).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [HardSphereB5.Lean.Pt, SphereGeom.E3, finrank_euclideanSpace])).ge
private theorem AS4B.B4a51 (b : B4a0) (i : Fin 4) (u : Pt) :
    inner ℝ (B4a39 b i 0) u • B4a39 b i 0 +
      inner ℝ (B4a40 b i 0) u • B4a40 b i 0 +
      inner ℝ (B4a10 b i 0) u • B4a10 b i 0 = u := by
  have h := (B4a53 b i).sum_repr' u
  simpa only [B4a53,OrthonormalBasis.coe_mk,Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using h
private def AS4B.B4a107 (b : B4a0) (i : Fin 4) : E2 →L[ℝ] Pt where
  toFun y := y 0 • B4a39 b i 0 + y 1 • B4a40 b i 0
  map_add' x y := by simp only [PiLp.add_apply,add_smul]; module
  map_smul' a y := by
    change (a*y 0) • B4a39 b i 0+(a*y 1) • B4a40 b i 0 =
      a • (y 0 • B4a39 b i 0+y 1 • B4a40 b i 0)
    simp only [smul_add,smul_smul]
  cont := by fun_prop
private def AS4B.B4a80 (b : B4a0) (i : Fin 4) (y : E2) : Pt :=
  B4a10 b i 0 + B4a107 b i y
private def AS4B.B4a68 (b : B4a0) (i : Fin 4) (y : E2) : Pt :=
  ‖B4a80 b i y‖⁻¹ • B4a80 b i y
private def AS4B.B4a90 (b : B4a0) (i : Fin 4) : Set E2 :=
  {y | ∀ j : Fin 3, (‖b.c (B4a94 b i j)-b.c i‖^2/2)*‖B4a80 b i y‖ ≤
    inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a80 b i y)}
private theorem AS4B.B4a81 (b : B4a0) (i : Fin 4) (y : E2) :
    inner ℝ (B4a10 b i 0) (B4a80 b i y) = 1 := by
  change inner ℝ (B4a10 b i 0)
    (B4a10 b i 0+(y 0 • B4a39 b i 0+y 1 • B4a40 b i 0)) = 1
  simp only [inner_add_right,real_inner_smul_right,(B4a50 b i 0).aa,
    (B4a50 b i 0).ae1,(B4a50 b i 0).ae2,mul_zero,add_zero]
private theorem AS4B.B4a82 (b : B4a0) (i : Fin 4) (y : E2) :
    inner ℝ (B4a39 b i 0) (B4a80 b i y) = y 0 := by
  have F:=B4a50 b i 0
  have he : inner ℝ (B4a39 b i 0) (B4a10 b i 0) = 0 := by rw [real_inner_comm];exact F.ae1
  change inner ℝ (B4a39 b i 0)
    (B4a10 b i 0+(y 0 • B4a39 b i 0+y 1 • B4a40 b i 0)) = y 0
  simp only [inner_add_right,real_inner_smul_right,he,F.e11,F.e12,
    mul_zero,mul_one,zero_add,add_zero]
private theorem AS4B.B4a83 (b : B4a0) (i : Fin 4) (y : E2) :
    inner ℝ (B4a40 b i 0) (B4a80 b i y) = y 1 := by
  have F:=B4a50 b i 0
  have he : inner ℝ (B4a40 b i 0) (B4a10 b i 0) = 0 := by rw [real_inner_comm];exact F.ae2
  have hf : inner ℝ (B4a40 b i 0) (B4a39 b i 0) = 0 := by rw [real_inner_comm];exact F.e12
  change inner ℝ (B4a40 b i 0)
    (B4a10 b i 0+(y 0 • B4a39 b i 0+y 1 • B4a40 b i 0)) = y 1
  simp only [inner_add_right,real_inner_smul_right,he,hf,F.e22,
    mul_zero,mul_one,zero_add,add_zero]
private theorem AS4B.B4a85 (b : B4a0) (i : Fin 4) (y : E2) : B4a80 b i y ≠ 0 := by
  intro he
  have h:=B4a81 b i y
  rw [he,inner_zero_right] at h
  norm_num at h
private theorem AS4B.B4a86 (b : B4a0) (i : Fin 4) (y : E2) : 0 < ‖B4a80 b i y‖ :=
  norm_pos_iff.mpr (B4a85 b i y)
private theorem AS4B.B4a73 (b : B4a0) (i : Fin 4) (y : E2) : ‖B4a68 b i y‖ = 1 := by
  rw [B4a68,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (B4a86 b i y).ne']
private theorem AS4B.B4a70 (b : B4a0) (i : Fin 4) (y : E2) :
    inner ℝ (B4a10 b i 0) (B4a68 b i y) = ‖B4a80 b i y‖⁻¹ := by
  rw [B4a68,real_inner_smul_right,B4a81,mul_one]
private theorem AS4B.B4a113 (b : B4a0) (i : Fin 4) (y : E2) :
    B4a108 b i (b.c i+B4a68 b i y) = y := by
  have ht : (‖B4a80 b i y‖⁻¹) ≠ 0 := inv_ne_zero (B4a86 b i y).ne'
  ext k
  fin_cases k
  · change inner ℝ (B4a39 b i 0) (b.c i+B4a68 b i y-b.c i) /
      inner ℝ (B4a10 b i 0) (b.c i+B4a68 b i y-b.c i) = y 0
    rw [add_sub_cancel_left,B4a70,B4a68,real_inner_smul_right,B4a82]
    exact mul_div_cancel_left₀ (y 0) ht
  · change inner ℝ (B4a40 b i 0) (b.c i+B4a68 b i y-b.c i) /
      inner ℝ (B4a10 b i 0) (b.c i+B4a68 b i y-b.c i) = y 1
    rw [add_sub_cancel_left,B4a70,B4a68,real_inner_smul_right,B4a83]
    exact mul_div_cancel_left₀ (y 1) ht
private theorem AS4B.B4a88 (b : B4a0) (i : Fin 4) (p : Pt)
    (ht : inner ℝ (B4a10 b i 0) (p-b.c i) ≠ 0) :
    B4a80 b i (B4a108 b i p) =
      (inner ℝ (B4a10 b i 0) (p-b.c i))⁻¹ • (p-b.c i) := by
  have h:=B4a51 b i (p-b.c i)
  calc
    _ = (inner ℝ (B4a10 b i 0) (p-b.c i))⁻¹ •
        (inner ℝ (B4a39 b i 0) (p-b.c i) • B4a39 b i 0+
         inner ℝ (B4a40 b i 0) (p-b.c i) • B4a40 b i 0+
         inner ℝ (B4a10 b i 0) (p-b.c i) • B4a10 b i 0) := by
      change B4a10 b i 0+
        ((inner ℝ (B4a39 b i 0) (p-b.c i)/inner ℝ (B4a10 b i 0) (p-b.c i)) • B4a39 b i 0+
         (inner ℝ (B4a40 b i 0) (p-b.c i)/inner ℝ (B4a10 b i 0) (p-b.c i)) • B4a40 b i 0) = _
      simp only [smul_add,smul_smul,div_eq_mul_inv,inv_mul_cancel₀ ht,one_smul]
      module
    _ = _ := by rw [h]
private theorem AS4B.B4a95 (b : B4a0) (i k : Fin 4) (hki : k ≠ i) :
    ∃ j, B4a94 b i j = k := by
  have ho : ∃ j, B4a98 i j = k := by
    fin_cases i <;> fin_cases k <;> simp_all [B4a98] <;> decide
  rcases ho with ⟨j,hj⟩
  unfold B4a94
  dsimp only
  split_ifs
  · have hf : Function.Surjective B4a48 := (Finite.injective_iff_surjective).mp B4a49
    rcases hf j with ⟨j',hj'⟩
    exact ⟨j',by rw [hj'];exact hj⟩
  · exact ⟨j,hj⟩
private theorem AS4B.B4a84 (b : B4a0) (i : Fin 4) (y : E2) :
    B4a80 b i y = (inner ℝ (B4a10 b i 0) (B4a68 b i y))⁻¹ • B4a68 b i y := by
  rw [B4a70,inv_inv,B4a68,← mul_smul,
    mul_inv_cancel₀ (B4a86 b i y).ne',one_smul]
private theorem AS4B.B4a72 (b : B4a0) (i : Fin 4) (y : E2)
    (hy : y ∈ B4a90 b i) : b.c i+B4a68 b i y ∈ patch b.c i := by
  have hu:=B4a73 b i y
  have ht : 0 < inner ℝ (B4a10 b i 0) (B4a68 b i y) := by
    rw [B4a70];exact inv_pos.mpr (B4a86 b i y)
  constructor
  · change dist (b.c i+B4a68 b i y) (b.c i) = 1
    simpa only [dist_eq_norm,add_sub_cancel_left] using hu
  · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
    intro k
    change dist (b.c i+B4a68 b i y) (b.c k) ≤ 1
    by_cases hki : k = i
    · subst k
      simpa only [dist_eq_norm,add_sub_cancel_left,hu] using (le_refl (1:ℝ))
    · obtain ⟨j,hj⟩:=B4a95 b i k hki
      have hm : (‖b.c k-b.c i‖^2/2)*‖B4a80 b i y‖ ≤
        inner ℝ (b.c k-b.c i) (B4a80 b i y) := by
        have hh:=hy j
        simpa only [hj] using hh
      have hb:= (AS4S.unit_ball_iff_norm_affine (B4a10 b i 0) (B4a68 b i y)
        (b.c k-b.c i) (B4a107 b i).toLinearMap y
        (inner ℝ (B4a10 b i 0) (B4a68 b i y)) hu ht
        (B4a84 b i y)).mpr hm
      have hd : dist (B4a68 b i y) (b.c k-b.c i) =
          dist (b.c i+B4a68 b i y) (b.c k) := by
        rw [dist_eq_norm,dist_eq_norm]
        congr 1
        abel
      rwa [hd] at hb
private theorem AS4B.B4a114 (b : B4a0) (i : Fin 4) (p : Pt)
    (hp : p ∈ patch b.c i) : B4a108 b i p ∈ B4a90 b i := by
  have hu : ‖p-b.c i‖ = 1 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
  have ht:=B4a106 b i p hp
  intro j
  have hb : dist (p-b.c i) (b.c (B4a94 b i j)-b.c i) ≤ 1 := by
    have hk:=hp.2
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
    have h:=hk (B4a94 b i j)
    change dist p (b.c (B4a94 b i j)) ≤ 1 at h
    have he : dist (p-b.c i) (b.c (B4a94 b i j)-b.c i) =
        dist p (b.c (B4a94 b i j)) := by
      rw [dist_eq_norm,dist_eq_norm];congr 1;abel
    rwa [he]
  exact (AS4S.unit_ball_iff_norm_affine (B4a10 b i 0) (p-b.c i)
    (b.c (B4a94 b i j)-b.c i) (B4a107 b i).toLinearMap
    (B4a108 b i p) (inner ℝ (B4a10 b i 0) (p-b.c i)) hu ht
    (B4a88 b i p ht.ne')).mp hb
private theorem AS4B.B4a5 (b : B4a0) (i : Fin 4) : B4a1 b i = B4a90 b i := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact B4a114 b i p hp
  · intro hy
    exact ⟨b.c i+B4a68 b i y, B4a72 b i y hy, B4a113 b i y⟩
private theorem AS4B.B4a4 (b : B4a0) (i : Fin 4) : Convex ℝ (B4a1 b i) := by
  rw [B4a5]
  exact AS4S.norm_affine_region_convex (B4a10 b i 0) (B4a107 b i).toLinearMap
    (fun j : Fin 3 => b.c (B4a94 b i j)-b.c i)
private theorem AS4B.B4a154 (b : B4a0) (l : Fin 4) :
    dist (B4a150 b l) (b.c l) < 1 := by
  have hk:=(B4a153 b l).2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
  have hl : dist (B4a150 b l) (b.c l) ≤ 1 := hk l
  apply lt_of_le_of_ne hl
  intro he
  apply B4a93 b (B4a150 b l)
  intro m
  by_cases hml : m = l
  · subst m;exact he
  · exact (B4a153 b l).1 m hml
private def AS4B.B4a126 (b : B4a0) (i : Fin 4) (j : Fin 3) : Pt :=
  B4a150 b (B4a94 b i j)-b.c i
private theorem AS4B.B4a127 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ‖B4a126 b i j‖ = 1 := by
  have h:=(B4a153 b (B4a94 b i j)).1 i (B4a97 b i j).symm
  simpa only [dist_eq_norm,B4a126] using h
private theorem AS4B.B4a128 (b : B4a0) (i : Fin 4) (j k : Fin 3) :
    ‖b.c (B4a94 b i j)-b.c i‖^2/2 ≤
      inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a126 b i k) := by
  have h:=(B4a153 b (B4a94 b i k)).2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at h
  have hb : dist (B4a150 b (B4a94 b i k)) (b.c (B4a94 b i j)) ≤ 1 := h _
  have ht : B4a126 b i k-(b.c (B4a94 b i j)-b.c i) =
      B4a150 b (B4a94 b i k)-b.c (B4a94 b i j) := by unfold B4a126;abel
  have he:=norm_sub_sq_real (B4a126 b i k) (b.c (B4a94 b i j)-b.c i)
  rw [B4a127,real_inner_comm] at he
  have hh : ‖B4a126 b i k-(b.c (B4a94 b i j)-b.c i)‖ ≤ 1 := by
    rw [ht];simpa only [dist_eq_norm] using hb
  nlinarith [norm_nonneg (B4a126 b i k-(b.c (B4a94 b i j)-b.c i))]
private theorem AS4B.B4a129 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ‖b.c (B4a94 b i j)-b.c i‖^2/2 <
      inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a126 b i j) := by
  have hb:=B4a154 b (B4a94 b i j)
  have ht : B4a126 b i j-(b.c (B4a94 b i j)-b.c i) =
      B4a150 b (B4a94 b i j)-b.c (B4a94 b i j) := by unfold B4a126;abel
  have he:=norm_sub_sq_real (B4a126 b i j) (b.c (B4a94 b i j)-b.c i)
  rw [B4a127,real_inner_comm] at he
  have hh : ‖B4a126 b i j-(b.c (B4a94 b i j)-b.c i)‖ < 1 := by
    rw [ht];simpa only [dist_eq_norm] using hb
  nlinarith [norm_nonneg (B4a126 b i j-(b.c (B4a94 b i j)-b.c i))]
private def AS4B.B4a122 (b : B4a0) (i : Fin 4) : Pt := ∑ j : Fin 3, B4a126 b i j
private theorem AS4B.B4a125 (b : B4a0) (i : Fin 4) : ‖B4a122 b i‖ ≤ 3 := by
  apply (norm_sum_le _ _).trans
  simp only [B4a127,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num
private theorem AS4B.B4a123 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    3*(‖b.c (B4a94 b i j)-b.c i‖^2/2) <
      inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a122 b i) := by
  have h:=Finset.sum_lt_sum (fun k (_ : k ∈ Finset.univ) => B4a128 b i j k)
    ⟨j,Finset.mem_univ _,B4a129 b i j⟩
  simpa only [B4a122,inner_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Nat.cast_ofNat,nsmul_eq_mul] using h
private theorem AS4B.B4a124 (b : B4a0) (i : Fin 4) : B4a122 b i ≠ 0 := by
  intro he
  have h:=B4a123 b i 0
  rw [he,inner_zero_right] at h
  have hn : 0 ≤ 3*(‖b.c (B4a94 b i 0)-b.c i‖^2/2) := by positivity
  linarith
private def AS4B.B4a65 (b : B4a0) (i : Fin 4) : Pt :=
  ‖B4a122 b i‖⁻¹ • B4a122 b i
private theorem AS4B.B4a67 (b : B4a0) (i : Fin 4) : ‖B4a65 b i‖ = 1 := by
  rw [B4a65,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ ‖B4a122 b i‖⁻¹),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (B4a124 b i))]
private theorem AS4B.B4a66 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ‖b.c (B4a94 b i j)-b.c i‖^2/2 <
      inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a65 b i) := by
  have hn : 0 < ‖B4a122 b i‖ := norm_pos_iff.mpr (B4a124 b i)
  have hle:=mul_le_mul_of_nonneg_right (B4a125 b i)
    (show 0 ≤ ‖b.c (B4a94 b i j)-b.c i‖^2/2 by positivity)
  have hlt:=lt_of_le_of_lt hle (B4a123 b i j)
  have h:=mul_lt_mul_of_pos_left hlt (inv_pos.mpr hn)
  rw [B4a65,real_inner_smul_right]
  calc
    _ = ‖B4a122 b i‖⁻¹ * (‖B4a122 b i‖*(‖b.c (B4a94 b i j)-b.c i‖^2/2)) := by
      rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]
    _ < _ := h
private theorem AS4B.B4a149 (b : B4a0) (i : Fin 4) (u : Pt) (hu : ‖u‖ = 1)
    (hcap : ∀ j : Fin 3, ‖b.c (B4a94 b i j)-b.c i‖^2/2 ≤
      inner ℝ (b.c (B4a94 b i j)-b.c i) u) : b.c i+u ∈ patch b.c i := by
  constructor
  · simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hu
  · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
    intro k
    change dist (b.c i+u) (b.c k) ≤ 1
    by_cases hki:k=i
    · subst k;simpa only [dist_eq_norm,add_sub_cancel_left,hu] using (le_refl (1:ℝ))
    · obtain ⟨j,hj⟩:=B4a95 b i k hki
      have hb:=hcap j
      rw [hj] at hb
      have he:=norm_sub_sq_real u (b.c k-b.c i)
      rw [hu,real_inner_comm] at he
      have hd : dist (b.c i+u) (b.c k) = ‖u-(b.c k-b.c i)‖ := by
        rw [dist_eq_norm];congr 1;abel
      rw [hd]
      nlinarith [norm_nonneg (u-(b.c k-b.c i))]
private theorem AS4B.B4a64 (b : B4a0) (i : Fin 4) :
    b.c i+B4a65 b i ∈ patch b.c i :=
  B4a149 b i _ (B4a67 b i)
    (fun j => (B4a66 b i j).le)
private theorem AS4B.B4a142 (b : B4a0) (i : Fin 4) :
    ∃ y : E2, ∀ j : Fin 3, 0 < B4a138 (B4a10 b i 0) (B4a107 b i)
      (b.c (B4a94 b i j)-b.c i) y := by
  let p:Pt:=b.c i+B4a65 b i
  have hp:p∈patch b.c i:=B4a64 b i
  have ht:=B4a106 b i p hp
  have hre:B4a80 b i (B4a108 b i p)=
      (inner ℝ (B4a10 b i 0) (p-b.c i))⁻¹ • B4a65 b i := by
    rw [B4a88 b i p ht.ne']
    simp only [p,add_sub_cancel_left]
  refine ⟨B4a108 b i p,?_⟩
  intro j
  have h:=mul_lt_mul_of_pos_left (B4a66 b i j) (inv_pos.mpr ht)
  change 0 < inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a80 b i (B4a108 b i p))-
    (‖b.c (B4a94 b i j)-b.c i‖^2/2)*‖B4a80 b i (B4a108 b i p)‖
  rw [hre,real_inner_smul_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le),
    B4a67,mul_one]
  nlinarith [h]
private theorem AS4B.B4a8 (b : B4a0) (i : Fin 4) :
    (interior (B4a1 b i)).Nonempty := by
  obtain ⟨y,hy⟩:=B4a142 b i
  let A:Set E2:= {x | ∀ j : Fin 3, 0 < B4a138 (B4a10 b i 0) (B4a107 b i)
    (b.c (B4a94 b i j)-b.c i) x}
  have hOpen:IsOpen A:=by
    have he:A=⋂j:Fin 3,{x | 0 < B4a138 (B4a10 b i 0) (B4a107 b i)
      (b.c (B4a94 b i j)-b.c i) x}:=by ext x;simp only [A,Set.mem_setOf_eq,Set.mem_iInter]
    rw [he]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (B4a140 _ _ _))
  have hsub:A ⊆ B4a1 b i:=by
    rw [B4a5]
    intro x hx j
    exact sub_nonneg.mp (hx j).le
  exact ⟨y,interior_maximal hsub hOpen hy⟩
private theorem AS4B.B4a74 (b : B4a0) (i : Fin 4) (p : Pt)
    (hp:p∈patch b.c i) : B4a68 b i (B4a108 b i p)=p-b.c i := by
  have hu:‖p-b.c i‖=1:=by simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
  have ht:=B4a106 b i p hp
  rw [B4a68,B4a88 b i p ht.ne',norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr ht.le),hu,mul_one,inv_inv,
    ←mul_smul,mul_inv_cancel₀ ht.ne',one_smul]
private theorem AS4B.B4a112 (b : B4a0) (i : Fin 4) :
    Set.InjOn (B4a108 b i) (patch b.c i) := by
  intro p hp q hq he
  have h:=congrArg (B4a68 b i) he
  rw [B4a74 b i p hp,B4a74 b i q hq] at h
  have hh:=congrArg (fun x : Pt => x+b.c i) h
  simpa only [sub_add_cancel] using hh
private theorem AS4B.B4a141 (b : B4a0) (i : Fin 4) (j : Fin 3) (y : E2) :
    (‖b.c (B4a94 b i j)-b.c i‖^2/2)*‖B4a80 b i y‖ =
      inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a80 b i y) ↔
    b.c i+B4a68 b i y ∈ Metric.sphere (b.c (B4a94 b i j)) 1 := by
  let v:Pt:=b.c (B4a94 b i j)-b.c i
  let u:Pt:=B4a68 b i y
  let R:ℝ:=‖B4a80 b i y‖
  have hR:0<R:=B4a86 b i y
  have hu:‖u‖=1:=B4a73 b i y
  have he:dist (b.c i+u) (b.c (B4a94 b i j))^2=
      1-2*inner ℝ v u+‖v‖^2:=by
    have hv:(b.c i+u)-b.c (B4a94 b i j)=u-v:=by dsimp [v];abel
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,real_inner_comm u v]
    ring
  have hid:inner ℝ v u=R⁻¹*inner ℝ v (B4a80 b i y):=by
    change inner ℝ v (R⁻¹ • B4a80 b i y)=_
    rw [real_inner_smul_right]
  have hmul:R*inner ℝ v u=inner ℝ v (B4a80 b i y):=by
    rw [hid,←mul_assoc,mul_inv_cancel₀ hR.ne',one_mul]
  change (‖v‖^2/2)*R=inner ℝ v (B4a80 b i y) ↔ _
  simp only [Metric.mem_sphere]
  constructor
  · intro h
    have hc:‖v‖^2/2=inner ℝ v u:=by nlinarith [hmul]
    nlinarith [dist_nonneg (x:=b.c i+u) (y:=b.c (B4a94 b i j))]
  · intro h
    have hc:‖v‖^2/2=inner ℝ v u:=by nlinarith [he]
    calc _ = R*inner ℝ v u := by rw [hc];ring
         _ = _ := hmul
private theorem AS4B.B4a6 (b : B4a0) (i : Fin 4) :
    frontier (B4a1 b i) = {y : E2 | y ∈ B4a90 b i ∧
      ∃ j : Fin 3, (‖b.c (B4a94 b i j)-b.c i‖^2/2)*‖B4a80 b i y‖ =
        inner ℝ (b.c (B4a94 b i j)-b.c i) (B4a80 b i y)} := by
  obtain ⟨w,hw⟩:=B4a142 b i
  rw [B4a5]
  exact B4a143 (B4a10 b i 0) (B4a107 b i)
    (fun j : Fin 3 => b.c (B4a94 b i j)-b.c i) w hw
private theorem AS4B.B4a7 (b : B4a0) (i : Fin 4) :
    frontier (B4a1 b i) = ⋃ j : Fin 3, B4a108 b i ''
      (patch b.c i ∩ Metric.sphere (b.c (B4a94 b i j)) 1) := by
  rw [B4a6]
  ext y
  simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_image,Set.mem_inter_iff]
  constructor
  · rintro ⟨hy,j,hj⟩
    refine ⟨j,b.c i+B4a68 b i y,⟨B4a72 b i y hy,?_⟩,
      B4a113 b i y⟩
    exact (B4a141 b i j y).mp hj
  · rintro ⟨j,p,⟨hp,hj⟩,rfl⟩
    refine ⟨B4a114 b i p hp,j,?_⟩
    apply (B4a141 b i j (B4a108 b i p)).mpr
    have he:b.c i+B4a68 b i (B4a108 b i p)=p:=by
      rw [B4a74 b i p hp];abel
    rwa [he]
private def AS4B.B4a133 (b : B4a0) (i : Fin 4) : Pt ≃ₗᵢ[ℝ] Pt := (B4a53 b i).repr.symm
private theorem AS4B.B4a134 (b : B4a0) (i : Fin 4) (u:Pt) :
    (B4a133 b i).symm u = WithLp.toLp 2 ![inner ℝ (B4a39 b i 0) u,
      inner ℝ (B4a40 b i 0) u,inner ℝ (B4a10 b i 0) u] := by
  ext j
  simp only [B4a133,LinearIsometryEquiv.symm_symm,
    OrthonormalBasis.repr_apply_apply,B4a53,OrthonormalBasis.coe_mk]
  fin_cases j <;> rfl
private theorem AS4B.B4a110 (b : B4a0) (i : Fin 4) (p:Pt) :
    B4a108 b i p=Gnomonic.chartFrame (B4a133 b i) (p-b.c i) := by
  rw [Gnomonic.chartFrame,B4a134]
  rfl
private theorem AS4B.B4a135 (b : B4a0) (i : Fin 4) (y:E2) :
    B4a133 b i (WithLp.toLp 2 ![y 0,y 1,1])=B4a80 b i y := by
  have h:=(B4a53 b i).sum_repr_symm (WithLp.toLp 2 ![y 0,y 1,1])
  simp only [B4a53,OrthonormalBasis.coe_mk,Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons,one_smul] at h
  calc
    _ = y 0 • B4a39 b i 0+y 1 • B4a40 b i 0+B4a10 b i 0 := by
      simpa only [B4a133,B4a53] using h.symm
    _ = _ := by change _=B4a10 b i 0+(y 0 • B4a39 b i 0+y 1 • B4a40 b i 0);abel
private theorem AS4B.B4a87 (b : B4a0) (i : Fin 4) (y:E2) :
    ‖B4a80 b i y‖=Real.sqrt (1+‖y‖^2) := by
  rw [←B4a135,(B4a133 b i).norm_map]
  have hs:‖WithLp.toLp 2 ![y 0,y 1,1]‖^2=1+‖y‖^2:=by
    simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
    simp
    ring
  have hr:0≤1+‖y‖^2:=by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 ![y 0,y 1,1] : Pt),Real.sqrt_nonneg (1+‖y‖^2),Real.sq_sqrt hr]
private theorem AS4B.B4a71 (b : B4a0) (i : Fin 4) (y:E2) :
    B4a68 b i y=Gnomonic.inverseFrame (B4a133 b i) y := by
  rw [B4a68,B4a87,Gnomonic.inverseFrame,map_smul,B4a135]
private def AS4B.B4a119 (b : B4a0) (i : Fin 4) : Set Pt :=
  (fun p:Pt=>p-b.c i) '' patch b.c i
private theorem AS4B.B4a120 (b : B4a0) (i : Fin 4) :
    B4a119 b i ⊆ Gnomonic.hemisphereFrame (B4a133 b i) := by
  rintro u ⟨p,hp,rfl⟩
  constructor
  · simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
  · rw [B4a134]
    exact B4a106 b i p hp
private theorem AS4B.B4a2 (b : B4a0) (i : Fin 4) :
    B4a1 b i=Gnomonic.chartFrame (B4a133 b i) '' B4a119 b i := by
  unfold B4a1 B4a119
  rw [←Set.image_comp]
  congr 1
  funext p
  exact B4a110 b i p
private theorem AS4B.B4a121 (b : B4a0) (i : Fin 4) :
    MeasurableSet (B4a119 b i) :=
  ((B4a104 b.c i).image (continuous_id.sub continuous_const)).isClosed.measurableSet
end AS4Scope16
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope17
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 cross2)
private theorem AS4B.B4a26 (b : B4a0) (i : Fin 4) (z : Pt)
    (hz:z≠0) (hp:inner ℝ (B4a10 b i 0) z=0) : B4a24 b i z ≠ 0 := by
  intro he
  have h0:inner ℝ (B4a39 b i 0) z=0:=by
    have h:=congrArg (fun x:E2=>x 0) he
    exact h
  have h1:inner ℝ (B4a40 b i 0) z=0:=by
    have h:=congrArg (fun x:E2=>x 1) he
    exact h
  have h:=B4a51 b i z
  simp only [h0,h1,hp,zero_smul,zero_add] at h
  exact hz h.symm
private theorem AS4B.B4a109 (n u v : Pt) (ht:inner ℝ u n≠0) :
    inner ℝ n (Gnomonic.projectVelocity n u v)=0:=by
  unfold Gnomonic.projectVelocity
  have ht':inner ℝ n u ≠ 0:=by rwa [real_inner_comm]
  simp only [inner_add_right,real_inner_smul_right]
  field_simp [ht']
  simp only [real_inner_comm u n,real_inner_comm v n]
  ring
private theorem AS4B.B4a60 (b : B4a0) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:B4a13 b i j t∈patch b.c i) :
    B4a55 b i j =ᶠ[nhds t] B4a54 b i j := by
  let f:ℝ→ℝ:=fun s=>inner ℝ (B4a10 b i 0) (B4a13 b i j s-b.c i)
  have hc:Continuous f:=by
    unfold f
    exact continuous_const.inner ((B4a19 b i j).continuous.sub continuous_const)
  have hOpen:IsOpen {s:ℝ|B4a46 b i<f s}:=isOpen_lt continuous_const hc
  have ht:B4a46 b i<f t:=by
    have h:=B4a105 b i (B4a13 b i j t) hp
    have hd:=(B4a38 b i 0).1
    change dist (b.c i) (b.c (B4a94 b i 0))/4<f t
    dsimp [f] at *
    linarith
  have hMem:{s:ℝ|B4a46 b i<f s}∈nhds t:=hOpen.mem_nhds ht
  filter_upwards [hMem] with s hs
  exact B4a58 b i j s hs.le
private theorem AS4B.B4a148 (b : B4a0) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:B4a13 b i j t∈patch b.c i) :
    HasDerivAt (B4a147 b i j)
      (Gnomonic.projectVelocity (B4a10 b i 0) (B4a13 b i j t-b.c i)
        (Gnomonic.capVelocity (B4a39 b i j) (B4a40 b i j) (B4a63 b i j) t)) t ∧
    Gnomonic.projectVelocity (B4a10 b i 0) (B4a13 b i j t-b.c i)
        (Gnomonic.capVelocity (B4a39 b i j) (B4a40 b i j) (B4a63 b i j) t)≠0:=by
  let h:ℝ:=B4a63 b i j
  have hh:|h|<1:=by
    change |dist (b.c i) (b.c (B4a94 b i j))/2| < 1
    rw [abs_of_pos (half_pos (B4a38 b i j).1)]
    change dist (b.c i) (b.c (B4a94 b i j))/2<1
    linarith [(B4a38 b i j).2]
  have he:B4a147 b i j=Gnomonic.projectedArc (B4a10 b i 0) (B4a10 b i j)
      (B4a39 b i j) (B4a40 b i j) h:=by
    funext s
    unfold B4a147 Gnomonic.projectedArc
    exact congrArg (Gnomonic.project (B4a10 b i 0)) (B4a20 b i j s)
  have hvis:t∈Gnomonic.visible (B4a10 b i 0) (B4a10 b i j)
      (B4a39 b i j) (B4a40 b i j) h:=by
    change 0 < inner ℝ (Gnomonic.capArc (B4a10 b i j) (B4a39 b i j) (B4a40 b i j)
      (dist (b.c i) (b.c (B4a94 b i j))/2) t) (B4a10 b i 0)
    rw [←B4a20,real_inner_comm]
    exact B4a106 b i _ hp
  have H:=(Gnomonic.capArc_regular (B4a10 b i 0) (B4a10 b i j)
    (B4a39 b i j) (B4a40 b i j) h (B4a50 b i j) hh (B4a50 b i 0).aa).2.2 t hvis
  rw [he,B4a20]
  exact ⟨H.2.2.1,H.2.2.2⟩
private theorem AS4B.B4a57 (b : B4a0) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:B4a13 b i j t∈patch b.c i) :
    deriv (B4a55 b i j) t = B4a24 b i
      (Gnomonic.projectVelocity (B4a10 b i 0) (B4a13 b i j t-b.c i)
        (Gnomonic.capVelocity (B4a39 b i j) (B4a40 b i j) (B4a63 b i j) t)) := by
  rw [(B4a60 b i j t hp).deriv_eq]
  have H:=(B4a148 b i j t hp).1
  have hd:= (B4a24 b i).hasFDerivAt.comp_hasDerivAt t H
  have he:B4a54 b i j=fun s=>B4a24 b i (B4a147 b i j s):=by
    funext s
    exact (B4a28 b i (B4a13 b i j s)).symm
  rw [he]
  exact hd.deriv
private theorem AS4B.B4a62 (b : B4a0) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:B4a13 b i j t∈patch b.c i) : deriv (B4a55 b i j) t≠0:=by
  rw [B4a57 b i j t hp]
  apply B4a26 b i
    (Gnomonic.projectVelocity (B4a10 b i 0) (B4a13 b i j t-b.c i)
        (Gnomonic.capVelocity (B4a39 b i j) (B4a40 b i j) (B4a63 b i j) t))
    (B4a148 b i j t hp).2
  apply B4a109
  rw [real_inner_comm]
  exact (B4a106 b i _ hp).ne'
private theorem AS4B.B4a103 (b : B4a0) (i : Fin 4) (j : Fin 3) (p : Pt)
    (hp:p∈patch b.c i) : B4a63 b i j ≤ inner ℝ (B4a10 b i j) (p-b.c i) := by
  have hk:=hp.2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
  have hb:=(CircleArc.ball_iff_inner (b.c i) (b.c (B4a94 b i j)) p hp.1).mp (hk _)
  have hd:=(B4a38 b i j).1
  have H:=mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
  have he:(dist (b.c i) (b.c (B4a94 b i j)))⁻¹ *
      (dist (b.c i) (b.c (B4a94 b i j))^2/2)=B4a63 b i j:=by
    unfold B4a63
    field_simp
  rw [he] at H
  rw [B4a10,real_inner_smul_left,real_inner_comm]
  exact H
private theorem AS4B.B4a14 (b : B4a0) (i : Fin 4) (j : Fin 3) (t:ℝ) :
    inner ℝ (B4a10 b i j) (B4a13 b i j t-b.c i)=B4a63 b i j := by
  rw [B4a20]
  have F:=B4a50 b i j
  simp only [Gnomonic.capArc,inner_add_right,real_inner_smul_right,F.aa,F.ae1,F.ae2,
    mul_one,mul_zero,zero_add,add_zero]
  rfl
private theorem AS4B.B4a11 (b : B4a0) (i : Fin 4) (j : Fin 3) (t:ℝ) :
    Gnomonic.capVelocity (B4a39 b i j) (B4a40 b i j) (B4a63 b i j) t =
      SphereGeom.cross (B4a10 b i j) (B4a13 b i j t-b.c i) := by
  rw [B4a20]
  exact B4a12 _ _ _ _ (B4a50 b i j).aa (B4a50 b i j).ae1
private theorem AS4B.B4a61 (b : B4a0) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (ht:B4a13 b i j t∈patch b.c i) (x:E2) (hx:x∈B4a1 b i) :
    0 ≤ cross2 (deriv (B4a55 b i j) t) (x-B4a55 b i j t) := by
  obtain ⟨p,hp,rfl⟩:=hx
  have hu:inner ℝ (B4a13 b i j t-b.c i) (B4a13 b i j t-b.c i)=1:=by
    have H:‖B4a13 b i j t-b.c i‖=1:=by
      simpa only [Metric.mem_sphere,dist_eq_norm] using ht.1
    rw [real_inner_self_eq_norm_sq,H];norm_num
  have hw:inner ℝ (p-b.c i) (p-b.c i)=1:=by
    have H:‖p-b.c i‖=1:=by simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
    rw [real_inner_self_eq_norm_sq,H];norm_num
  have hh:0≤B4a63 b i j:=(half_pos (B4a38 b i j).1).le
  have H:=B4a29 b i (B4a10 b i j) (B4a13 b i j t-b.c i)
    (p-b.c i) (B4a63 b i j) hu hw hh (B4a14 b i j t)
    (B4a103 b i j p hp) (B4a106 b i _ ht)
    (B4a106 b i _ hp)
  rw [B4a57 b i j t ht,B4a11,
    B4a59 b i j t ht]
  simpa only [map_sub,B4a28,B4a54] using H
end AS4Scope17
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope18
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 PositiveConvexBoundary cross2)
private theorem AS4B.B4a185 (b : B4a0) (i m : Fin 4) (hmi : m ≠ i) :
    ∃ j : Fin 3, B4a94 b i j = m := by
  have hothers : ∀ (i m : Fin 4), m ≠ i → ∃ j : Fin 3, B4a98 i j = m := by decide
  obtain ⟨j,hj⟩ := hothers i m hmi
  have hinv : ∀ j : Fin 3, B4a48 (B4a48 j) = j := by decide
  dsimp only [B4a94]
  split_ifs
  · exact ⟨B4a48 j,by rw [hinv,hj]⟩
  · exact ⟨j,hj⟩
private theorem AS4B.B4a203 : ∀ (j k : Fin 3),
    k = j ∨ k = j+1 ∨ k = (j+1)+1 := by decide
private theorem AS4B.B4a187 : ∀ j : Fin 3, j+1 ≠ (j+1)+1 := by decide
private theorem AS4B.B4a202 (b : B4a0) (i : Fin 4) (j : Fin 3) (p : Pt)
    (hpair : p ∈ Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1)
    (hK : p ∈ Kset b.c) (m : Fin 4) (hmi : m ≠ i) (hmj : m ≠ B4a94 b i j)
    (hsm : dist p (b.c m) = 1) :
    p = B4a144 b i j ∨ p = B4a42 b i j := by
  obtain ⟨k,hk⟩ := B4a185 b i m hmi
  have hkj : k ≠ j := fun h => hmj (by rw [← hk,h])
  rcases B4a203 j k with he | he | he
  · exact (hkj he).elim
  · have htr : p ∈ triplePts b.c (B4a94 b i ((j+1)+1)) := by
      intro a ha
      by_cases hai : a = i
      · subst a; exact hpair.1
      · obtain ⟨r,hr⟩ := B4a185 b i a hai
        rcases B4a203 j r with her | her | her
        · rw [← hr,her]; exact hpair.2
        · rw [← hr,her,← he,hk]; exact hsm
        · exact (ha (by rw [← hr,her])).elim
    have hmem : p ∈ triplePts b.c (B4a94 b i ((j+1)+1)) ∩ Kset b.c := ⟨htr,hK⟩
    rw [B4a130] at hmem
    exact Or.inr (Set.mem_singleton_iff.mp hmem)
  · have htr : p ∈ triplePts b.c (B4a94 b i (j+1)) := by
      intro a ha
      by_cases hai : a = i
      · subst a; exact hpair.1
      · obtain ⟨r,hr⟩ := B4a185 b i a hai
        rcases B4a203 j r with her | her | her
        · rw [← hr,her]; exact hpair.2
        · exact (ha (by rw [← hr,her])).elim
        · rw [← hr,her,← he,hk]; exact hsm
    have hmem : p ∈ triplePts b.c (B4a94 b i (j+1)) ∩ Kset b.c := ⟨htr,hK⟩
    rw [B4a130] at hmem
    exact Or.inl (Set.mem_singleton_iff.mp hmem)
private theorem AS4B.B4a161 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    Set.InjOn (B4a13 b i j) (Set.Ico 0 (2*Real.pi)) := by
  intro x hx y hy hxy
  have hspan : max x y-min x y < 2*Real.pi := by
    have hl : 0 ≤ min x y := le_min hx.1 hy.1
    have hu : max x y < 2*Real.pi := max_lt hx.2 hy.2
    linarith
  have hi := B4a17 (B4a89 b i j) ![B4a39 b i j,B4a40 b i j]
    (B4a52 b i j) (B4a116 b i j) (B4a117 b i j)
    (min x y) (max x y) hspan
  exact hi ⟨min_le_left _ _,le_max_left _ _⟩ ⟨min_le_right _ _,le_max_right _ _⟩ hxy
private theorem AS4B.B4a199 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2*Real.pi)) (hK : B4a13 b i j t ∈ Kset b.c)
    (m : Fin 4) (hmi : m ≠ i) (hmj : m ≠ B4a94 b i j)
    (hsm : dist (B4a13 b i j t) (b.c m) = 1) :
    t = 0 ∨ t = B4a75 b i j := by
  have hp := B4a202 b i j (B4a13 b i j t)
    (B4a18 b i j t) hK m hmi hmj hsm
  have hi := B4a161 b i j
  rcases hp with hp | hp
  · left
    exact hi ht ⟨le_rfl,by positivity⟩ (hp.trans (B4a21 b i j).symm)
  · right
    exact hi ht ⟨(B4a79 b i j).le,B4a77 b i j⟩
      (hp.trans (B4a16 b i j).symm)
private def AS4B.B4a195 (b : B4a0) (i : Fin 4) (j k : Fin 3) (t : ℝ) : ℝ :=
  inner ℝ (b.c (B4a94 b i k)-b.c i) (B4a13 b i j t-b.c i)-
    ‖b.c (B4a94 b i k)-b.c i‖^2/2
private def AS4B.B4a174 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) : ℝ :=
  min (B4a195 b i j (j+1) t) (B4a195 b i j ((j+1)+1) t)
private theorem AS4B.B4a197 (b : B4a0) (i : Fin 4) (j k : Fin 3) :
    Continuous (B4a195 b i j k) := by
  unfold B4a195 B4a13 SphereGeom.circlePt
  fun_prop
private theorem AS4B.B4a175 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    Continuous (B4a174 b i j) :=
  (B4a197 b i j (j+1)).min (B4a197 b i j ((j+1)+1))
private theorem AS4B.B4a196 (b : B4a0) (i : Fin 4) (j k : Fin 3) (t : ℝ) :
    0 ≤ B4a195 b i j k t ↔ B4a13 b i j t ∈ Metric.closedBall (b.c (B4a94 b i k)) 1 := by
  have h := CircleArc.ball_iff_inner (b.c i) (b.c (B4a94 b i k)) (B4a13 b i j t)
    (B4a18 b i j t).1
  have hn : ‖b.c (B4a94 b i k)-b.c i‖^2 = dist (b.c i) (b.c (B4a94 b i k))^2 := by
    rw [← dist_eq_norm,dist_comm]
  simp only [B4a195,sub_nonneg,hn]
  simpa only [real_inner_comm] using h.symm
private theorem AS4B.B4a178 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    0 ≤ B4a174 b i j t ↔ B4a13 b i j t ∈ Kset b.c := by
  rw [B4a174,le_min_iff,B4a196,B4a196]
  constructor
  · rintro ⟨hk,hl⟩
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
    intro m
    by_cases hm : m = i
    · subst m; exact (B4a18 b i j t).1.le
    · obtain ⟨k,hk'⟩ := B4a185 b i m hm
      rcases B4a203 j k with he | he | he
      · rw [← hk',he]; exact (B4a18 b i j t).2.le
      · rw [← hk',he]; exact hk
      · rw [← hk',he]; exact hl
  · intro hK
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hK
    exact ⟨hK _,hK _⟩
private theorem AS4B.B4a198 (b : B4a0) (i : Fin 4) (j k : Fin 3) (t : ℝ) :
    B4a195 b i j k t = 0 ↔ dist (B4a13 b i j t) (b.c (B4a94 b i k)) = 1 := by
  let u := B4a13 b i j t-b.c i
  let v := b.c (B4a94 b i k)-b.c i
  have hu : ‖u‖ = 1 := (B4a18 b i j t).1
  have hsq : dist (B4a13 b i j t) (b.c (B4a94 b i k))^2 =
      1-2*inner ℝ v u+‖v‖^2 := by
    have hv : B4a13 b i j t-b.c (B4a94 b i k) = u-v := by dsimp [u,v]; abel
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu]
    rw [real_inner_comm]
    ring
  change inner ℝ v u-‖v‖^2/2 = 0 ↔ _
  constructor <;> intro h
  · nlinarith [dist_nonneg (x:=B4a13 b i j t) (y:=b.c (B4a94 b i k))]
  · rw [h] at hsq
    nlinarith
private theorem AS4B.B4a181 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2*Real.pi)) (hz : B4a174 b i j t = 0) :
    t = 0 ∨ t = B4a75 b i j := by
  have hK := (B4a178 b i j t).mp hz.ge
  have hmin : B4a195 b i j (j+1) t = 0 ∨ B4a195 b i j ((j+1)+1) t = 0 := by
    rcases le_total (B4a195 b i j (j+1) t) (B4a195 b i j ((j+1)+1) t) with h | h
    · exact Or.inl (by simpa only [B4a174,min_eq_left h] using hz)
    · exact Or.inr (by simpa only [B4a174,min_eq_right h] using hz)
  rcases hmin with h | h
  · exact B4a199 b i j t ht hK _ (B4a97 b i (j+1))
      (fun he => B4a92 j (B4a96 b i he).symm)
      ((B4a198 b i j (j+1) t).mp h)
  · exact B4a199 b i j t ht hK _ (B4a97 b i ((j+1)+1))
      (fun he => B4a91 j (B4a96 b i he).symm)
      ((B4a198 b i j ((j+1)+1) t).mp h)
private theorem AS4B.B4a200 (f : ℝ → ℝ) (hf : Continuous f) (a b s : ℝ)
    (hs : s ∈ Set.Ioo a b) (hfs : 0 < f s)
    (hzero : ∀ t ∈ Set.Ioo a b, f t ≠ 0) : ∀ t ∈ Set.Ioo a b, 0 < f t := by
  intro t ht
  by_contra h
  have hft : f t < 0 := lt_of_le_of_ne (le_of_not_gt h) (hzero t ht)
  have hmid := isPreconnected_Ioo.intermediate_value ht hs hf.continuousOn
  obtain ⟨r,hr,hfr⟩ := hmid (show 0 ∈ Set.Icc (f t) (f s) from ⟨hft.le,hfs.le⟩)
  exact hzero r hr hfr
private theorem AS4B.B4a166 (f : ℝ → ℝ) (d : ℝ) (h0 : f 0 = 0)
    (hf : HasDerivAt f d 0) (hd : 0 < d) :
    ∃ ε > 0, (∀ t, 0 < t → t < ε → 0 < f t) ∧
      (∀ t, -ε < t → t < 0 → f t < 0) := by
  have he := hf.isLittleO.def (half_pos hd)
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε,hε,?_,?_⟩
  · intro t ht hte
    have he' := he (y:=t) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using hte)
    simp only [h0,sub_zero,smul_eq_mul,Real.norm_eq_abs,abs_of_pos ht] at he'
    have hb := (abs_le.mp he').1
    nlinarith
  · intro t ht hte
    have he' := he (y:=t) (by rw [Real.dist_eq,sub_zero,abs_of_neg hte]; linarith)
    simp only [h0,sub_zero,smul_eq_mul,Real.norm_eq_abs,abs_of_neg hte] at he'
    have hb := (abs_le.mp he').2
    nlinarith
private def AS4B.B4a193 (X Y s : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0,1,1,Y], ![1,0,X,1], ![1,X,0,s], ![Y,1,s,0]]
private theorem AS4B.B4a194 (b : B4a0) (i j : Fin 4) : q b.c i j = B4a193 b.X b.Y b.s i j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact b.path.q01 | exact b.path.q02 | exact b.path.q03
    | exact b.path.q12 | exact b.path.q13 | exact b.path.q23
    | exact (q_symm' b.c 1 0).trans b.path.q01
    | exact (q_symm' b.c 2 0).trans b.path.q02
    | exact (q_symm' b.c 3 0).trans b.path.q03
    | exact (q_symm' b.c 2 1).trans b.path.q12
    | exact (q_symm' b.c 3 1).trans b.path.q13
    | exact (q_symm' b.c 3 2).trans b.path.q23
    | simp [q,B4a193]
private theorem AS4B.B4a186 (b : B4a0) (i a d l : Fin 4)
    (hia : i ≠ a) (hid : i ≠ d) (hil : i ≠ l)
    (had : a ≠ d) (hal : a ≠ l) (hdl : d ≠ l) :
    AS4T.faceDelta (b.c a-b.c i) (b.c d-b.c i) = Dpoly b.X b.Y b.s l ∧
    AS4T.faceQ (b.c a-b.c i) (b.c d-b.c i) = Qpoly b.X b.Y b.s l ∧
    4*(inner ℝ (b.c l-b.c i) (SphereGeom.cross (b.c a-b.c i) (b.c d-b.c i)))^2 = Hpoly b.X b.Y b.s := by
  have hg := gram_from_q b.c i a d l
  simp only [real_inner_comm] at hg
  rw [hg]
  simp only [AS4T.faceDelta,AS4T.faceQ,TG_sq_q,TG_sq_diff_q,
    B4a194]
  fin_cases i <;> fin_cases a <;> fin_cases d <;> fin_cases l <;> norm_num at *
  all_goals simp [gramPoly,DeltaT,QT,Dpoly,Qpoly,Hpoly,B4a193]
  all_goals constructor
  all_goals try constructor
  all_goals ring
private theorem AS4B.B4a182 (v w z u : Pt) (hD : 0 < AS4T.faceDelta v w)
    (hQ : 0 < AS4T.faceQ v w) (hG : inner ℝ z (SphereGeom.cross v w) ≠ 0)
    (hset : AS4T.triple v w ∩ Metric.closedBall z 1 = {u}) :
    u = AS4T.center v w+AS4T.height v w • AS4T.orientedNormal v w z := by
  let p := AS4T.center v w+AS4T.height v w • AS4T.orientedNormal v w z
  let m := AS4T.center v w-AS4T.height v w • AS4T.orientedNormal v w z
  have htr := AS4T.triple_exact v w z hD hQ
  have hu : u ∈ AS4T.triple v w ∩ Metric.closedBall z 1 := by rw [hset]; exact Set.mem_singleton _
  have ht := hu.1
  rw [htr] at ht
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
  rcases ht with ht | ht
  · exact ht
  · have hm : ‖m-z‖ ≤ 1 := by simpa only [ht,Metric.mem_closedBall,dist_eq_norm] using hu.2
    have hp := AS4T.fourth_sq_formula v w z (AS4T.height v w) hD hQ rfl
    have hn := AS4T.fourth_sq_formula v w z (-AS4T.height v w) hD hQ
      (neg_sq _)
    have hmform : ‖m-z‖^2-1 = AS4T.sq z-
        2*inner ℝ z (AS4T.center v w)+
        2*AS4T.height v w*inner ℝ z (AS4T.orientedNormal v w z) := by
      dsimp [m]
      simpa only [neg_smul,sub_eq_add_neg,neg_mul,mul_neg,sub_neg_eq_add,neg_neg] using hn
    have hpball : p ∈ Metric.closedBall z 1 := by
      have hh := AS4T.height_pos v w hD hQ
      have hh' := AS4T.normal_oriented v w z hD hG
      have hpn : ‖p-z‖ ≤ 1 := by
        change ‖p-z‖^2-1 = _ at hp
        nlinarith [norm_nonneg (p-z),norm_nonneg (m-z),mul_pos hh hh']
      exact hpn
    have hpt : p ∈ AS4T.triple v w := by
      rw [htr]
      exact Or.inl rfl
    have hpu : p = u := by
      have hh : p ∈ ({u} : Set Pt) := by
        rw [← hset]
        exact ⟨hpt,hpball⟩
      exact Set.mem_singleton_iff.mp hh
    have hpm := AS4T.triple_points_ne v w z hD hQ
    exact (hpm (hpu.trans ht)).elim
private theorem AS4B.B4a157 (b : B4a0) (i a d l : Fin 4)
    (hia : i ≠ a) (hid : i ≠ d) (hil : i ≠ l)
    (had : a ≠ d) (hal : a ≠ l) (hdl : d ≠ l) :
    B4a150 b l-b.c i = AS4T.center (b.c a-b.c i) (b.c d-b.c i)+
      AS4T.height (b.c a-b.c i) (b.c d-b.c i) •
        AS4T.orientedNormal (b.c a-b.c i) (b.c d-b.c i) (b.c l-b.c i) := by
  have hp := B4a186 b i a d l hia hid hil had hal hdl
  have hD : 0 < AS4T.faceDelta (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.1]; exact path_Dpoly_pos b.c b.X b.Y b.s b.path l
  have hQ : 0 < AS4T.faceQ (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.2.1]; exact path_Qpoly_pos b.c b.X b.Y b.s b.path l
  have hG : inner ℝ (b.c l-b.c i) (SphereGeom.cross (b.c a-b.c i) (b.c d-b.c i)) ≠ 0 := by
    intro hz; rw [hz] at hp; nlinarith [b.path.H_pos,hp.2.2]
  have hlabels : ∀ m : Fin 4, m = i ∨ m = a ∨ m = d ∨ m = l := by
    fin_cases i <;> fin_cases a <;> fin_cases d <;> fin_cases l <;> norm_num at *
    all_goals decide
  have hset : AS4T.triple (b.c a-b.c i) (b.c d-b.c i) ∩
      Metric.closedBall (b.c l-b.c i) 1 = {B4a150 b l-b.c i} := by
    ext u
    have he : u+b.c i ∈ triplePts b.c l ∩ Kset b.c ↔
        u ∈ AS4T.triple (b.c a-b.c i) (b.c d-b.c i) ∩
          Metric.closedBall (b.c l-b.c i) 1 := by
      constructor
      · rintro ⟨htr,hK⟩
        have hu := htr i hil
        have hua := htr a hal
        have hud := htr d hdl
        have hK' := hK
        simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hK'
        refine ⟨⟨?_,?_,?_⟩,?_⟩
        · simpa only [dist_eq_norm,add_sub_cancel_right] using hu
        · have hvec : u+b.c i-b.c a = u-(b.c a-b.c i) := by abel
          simpa only [dist_eq_norm,hvec] using hua
        · have hvec : u+b.c i-b.c d = u-(b.c d-b.c i) := by abel
          simpa only [dist_eq_norm,hvec] using hud
        · have hvec : u+b.c i-b.c l = u-(b.c l-b.c i) := by abel
          simpa only [Metric.mem_closedBall,dist_eq_norm,hvec] using hK' l
      · rintro ⟨⟨hu,hua,hud⟩,hul⟩
        have hdi : dist (u+b.c i) (b.c i) = 1 := by simpa only [dist_eq_norm,add_sub_cancel_right] using hu
        have hda : dist (u+b.c i) (b.c a) = 1 := by
          have hvec : u+b.c i-b.c a = u-(b.c a-b.c i) := by abel
          simpa only [dist_eq_norm,hvec] using hua
        have hdd : dist (u+b.c i) (b.c d) = 1 := by
          have hvec : u+b.c i-b.c d = u-(b.c d-b.c i) := by abel
          simpa only [dist_eq_norm,hvec] using hud
        have hdl' : dist (u+b.c i) (b.c l) ≤ 1 := by
          have hvec : u+b.c i-b.c l = u-(b.c l-b.c i) := by abel
          simpa only [Metric.mem_closedBall,dist_eq_norm,hvec] using hul
        constructor
        · intro m hml
          rcases hlabels m with rfl | rfl | rfl | rfl
          · exact hdi
          · exact hda
          · exact hdd
          · exact (hml rfl).elim
        · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
          intro m
          rcases hlabels m with rfl | rfl | rfl | rfl
          · exact hdi.le
          · exact hda.le
          · exact hdd.le
          · exact hdl'
    rw [← he,B4a130]
    simp only [Set.mem_singleton_iff,eq_sub_iff_add_eq]
  exact B4a182 _ _ _ _ hD hQ hG hset
private lemma AS4B.B4a168 (v w z : Pt) : det3 v z w = -det3 v w z := by
  simp only [det3,AS4T.inner_coords,AS4T.cross_coords]
  simp
  ring
private lemma AS4B.B4a167 (v w z : Pt) : det3 w z v = det3 v w z := by
  simp only [det3,AS4T.inner_coords,AS4T.cross_coords]
  simp
  ring
private lemma AS4B.B4a164 (v w : Pt) (a : ℝ) : SphereGeom.cross (a • v) w = a • SphereGeom.cross v w := by
  ext k
  fin_cases k <;> simp [AS4T.cross_coords] <;> ring
private lemma AS4B.B4a165 (v w : Pt) (a : ℝ) : SphereGeom.cross v (a • w) = a • SphereGeom.cross v w := by
  have hh := B4a36 v w (0 : Pt) a 0
  simpa only [zero_smul,add_zero] using hh
private theorem AS4B.B4a184 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    0 < det3 (b.c (B4a94 b i j)-b.c i)
      (b.c (B4a94 b i (j+1))-b.c i) (b.c (B4a94 b i ((j+1)+1))-b.c i) := by
  let v := b.c (B4a98 i 0)-b.c i
  let w := b.c (B4a98 i 1)-b.c i
  let z := b.c (B4a98 i 2)-b.c i
  have ho : ∀ j k : Fin 3, j ≠ k → B4a98 i j ≠ B4a98 i k :=
    fun j k h => fun he => h (B4a99 i he)
  have hp := B4a186 b i (B4a98 i 0) (B4a98 i 1) (B4a98 i 2)
    (B4a100 i 0).symm (B4a100 i 1).symm (B4a100 i 2).symm
    (ho 0 1 (by decide)) (ho 0 2 (by decide)) (ho 1 2 (by decide))
  have hz : det3 v w z ≠ 0 := by
    intro he
    have hg := hp.2.2
    change 4*(inner ℝ z (SphereGeom.cross v w))^2 = Hpoly b.X b.Y b.s at hg
    rw [real_inner_comm] at hg
    change 4*(det3 v w z)^2 = Hpoly b.X b.Y b.s at hg
    rw [he] at hg
    nlinarith [b.path.H_pos]
  have hfirst : 0 < det3 (b.c (B4a94 b i 0)-b.c i)
      (b.c (B4a94 b i 1)-b.c i) (b.c (B4a94 b i 2)-b.c i) := by
    unfold B4a94
    dsimp only
    change 0 < det3 (b.c (if det3 v w z < 0 then B4a98 i (B4a48 0) else B4a98 i 0)-b.c i)
      (b.c (if det3 v w z < 0 then B4a98 i (B4a48 1) else B4a98 i 1)-b.c i)
      (b.c (if det3 v w z < 0 then B4a98 i (B4a48 2) else B4a98 i 2)-b.c i)
    split_ifs with h
    · change 0 < det3 v z w
      rw [B4a168]
      exact neg_pos.mpr h
    · change 0 < det3 v w z
      exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hz)
  fin_cases j
  · simpa using hfirst
  · change 0 < det3 (b.c (B4a94 b i 1)-b.c i) (b.c (B4a94 b i 2)-b.c i)
      (b.c (B4a94 b i 0)-b.c i)
    rw [B4a167]; exact hfirst
  · change 0 < det3 (b.c (B4a94 b i 2)-b.c i) (b.c (B4a94 b i 0)-b.c i)
      (b.c (B4a94 b i 1)-b.c i)
    rw [B4a167,B4a167]; exact hfirst
private theorem AS4B.B4a183 (v w z : Pt) (hD : 0 < AS4T.faceDelta v w)
    (hQ : 0 < AS4T.faceQ v w) (hG : inner ℝ z (SphereGeom.cross v w) < 0) :
    0 < inner ℝ w (SphereGeom.cross v (AS4T.center v w+
      AS4T.height v w • AS4T.orientedNormal v w z)) := by
  have hN : AS4T.orientedNormal v w z = -(‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w) := by
    rw [AS4T.orientedNormal,if_neg (not_lt_of_ge hG.le)]
  have hC : inner ℝ w (SphereGeom.cross v (AS4T.center v w)) = 0 := by
    unfold AS4T.center
    rw [B4a36]
    simp only [inner_add_right,real_inner_smul_right,B4a37,
      AS4T.cross_w,inner_zero_right,mul_zero,zero_add]
  have hGram : inner ℝ w (SphereGeom.cross v (SphereGeom.cross v w)) = -AS4T.faceDelta v w/4 := by
    rw [B4a34,inner_sub_right,real_inner_smul_right,real_inner_smul_right]
    have hd := AS4T.delta_gram v w
    change AS4T.faceDelta v w = 4*(inner ℝ v v*inner ℝ w w-(inner ℝ v w)^2) at hd
    rw [real_inner_comm v w]
    nlinarith [hd]
  have hscale : inner ℝ w (SphereGeom.cross v (AS4T.orientedNormal v w z)) =
      ‖SphereGeom.cross v w‖⁻¹*(AS4T.faceDelta v w/4) := by
    rw [hN,show -(‖SphereGeom.cross v w‖⁻¹ • SphereGeom.cross v w) = (-‖SphereGeom.cross v w‖⁻¹) • SphereGeom.cross v w by rw [neg_smul],
      B4a165,real_inner_smul_right,hGram]
    ring
  have hh := B4a36 v (AS4T.center v w) (AS4T.orientedNormal v w z)
    1 (AS4T.height v w)
  rw [one_smul] at hh
  rw [hh,inner_add_right,real_inner_smul_right,real_inner_smul_right,hC,one_mul,zero_add,hscale]
  exact mul_pos (AS4T.height_pos v w hD hQ)
    (mul_pos (inv_pos.mpr (AS4T.cross_norm_pos v w hD)) (div_pos hD (by norm_num)))
private theorem AS4B.B4a158 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    0 < inner ℝ (b.c (B4a94 b i ((j+1)+1))-b.c i)
      (SphereGeom.cross (B4a10 b i j) (B4a144 b i j-b.c i)) := by
  let a := B4a94 b i j
  let d := B4a94 b i ((j+1)+1)
  let l := B4a94 b i (j+1)
  have had : a ≠ d := fun h => B4a91 j (B4a96 b i h)
  have hal : a ≠ l := fun h => B4a92 j (B4a96 b i h)
  have hdl : d ≠ l := fun h => B4a187 j (B4a96 b i h).symm
  have hp := B4a186 b i a d l (B4a97 b i j).symm
    (B4a97 b i ((j+1)+1)).symm (B4a97 b i (j+1)).symm had hal hdl
  have hr := B4a157 b i a d l (B4a97 b i j).symm
    (B4a97 b i ((j+1)+1)).symm (B4a97 b i (j+1)).symm had hal hdl
  have hG : inner ℝ (b.c l-b.c i) (SphereGeom.cross (b.c a-b.c i) (b.c d-b.c i)) < 0 := by
    have hg := B4a184 b i j
    have he := B4a168 (b.c a-b.c i) (b.c l-b.c i) (b.c d-b.c i)
    change det3 (b.c a-b.c i) (b.c d-b.c i) (b.c l-b.c i) = _ at he
    rw [real_inner_comm]
    change det3 (b.c a-b.c i) (b.c d-b.c i) (b.c l-b.c i) < 0
    rw [he]
    exact neg_neg_of_pos hg
  have hD : 0 < AS4T.faceDelta (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.1]; exact path_Dpoly_pos b.c b.X b.Y b.s b.path l
  have hQ : 0 < AS4T.faceQ (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.2.1]; exact path_Qpoly_pos b.c b.X b.Y b.s b.path l
  change 0 < inner ℝ (b.c d-b.c i) (SphereGeom.cross (B4a10 b i j) (B4a150 b l-b.c i))
  rw [hr,B4a10,B4a164,real_inner_smul_right]
  exact mul_pos (inv_pos.mpr (B4a38 b i j).1)
    (B4a183 _ _ _ hD hQ hG)
private theorem AS4B.B4a163 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    B4a13 b i j (t+2*Real.pi) = B4a13 b i j t := by
  simp only [B4a13,SphereGeom.circlePt,Real.cos_add_two_pi,Real.sin_add_two_pi]
private theorem AS4B.B4a179 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    B4a174 b i j (t+2*Real.pi) = B4a174 b i j t := by
  simp only [B4a174,B4a195,B4a163]
private theorem AS4B.B4a201 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    0 < B4a195 b i j (j+1) 0 ∧ B4a195 b i j ((j+1)+1) 0 = 0 := by
  have hp : B4a144 b i j ∈ Kset b.c := (B4a153 b (B4a94 b i (j+1))).2
  have hk : B4a13 b i j 0 ∈ Kset b.c := by rwa [B4a21]
  have hnon : 0 ≤ B4a195 b i j (j+1) 0 :=
    (le_min_iff.mp ((B4a178 b i j 0).mpr hk)).1
  have hne : B4a195 b i j (j+1) 0 ≠ 0 := by
    intro hz
    have hs := (B4a198 b i j (j+1) 0).mp hz
    rw [B4a21] at hs
    exact (ne_of_lt (B4a154 b (B4a94 b i (j+1)))) hs
  have hd : dist (B4a144 b i j) (b.c (B4a94 b i ((j+1)+1))) = 1 := by
    exact (B4a153 b (B4a94 b i (j+1))).1 _
      (fun he => B4a187 j (B4a96 b i he).symm)
  exact ⟨lt_of_le_of_ne hnon hne.symm,
    (B4a198 b i j ((j+1)+1) 0).mpr (by rwa [B4a21])⟩
private theorem AS4B.B4a180 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a174 b i j 0 = 0 := by
  have h := B4a201 b i j
  rw [B4a174,h.2,min_eq_right h.1.le]
private theorem AS4B.B4a177 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a174 b i j (B4a75 b i j) = 0 := by
  have hk : B4a13 b i j (B4a75 b i j) ∈ Kset b.c := by
    rw [B4a16]
    exact (B4a153 b (B4a94 b i ((j+1)+1))).2
  have hn := le_min_iff.mp ((B4a178 b i j _).mpr hk)
  have hs : dist (B4a13 b i j (B4a75 b i j)) (b.c (B4a94 b i (j+1))) = 1 := by
    rw [B4a16]
    exact (B4a153 b (B4a94 b i ((j+1)+1))).1 _
      (fun he => B4a187 j (B4a96 b i he))
  have hz := (B4a198 b i j (j+1) _).mpr hs
  rw [B4a174,hz,min_eq_left hn.2]
private theorem AS4B.B4a176 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    HasDerivAt (B4a174 b i j)
      (inner ℝ (b.c (B4a94 b i ((j+1)+1))-b.c i)
        (SphereGeom.cross (B4a10 b i j) (B4a144 b i j-b.c i))) 0 := by
  let v := b.c (B4a94 b i ((j+1)+1))-b.c i
  have hfun : B4a195 b i j ((j+1)+1) = fun t =>
      inner ℝ v (B4a89 b i j-b.c i)+B4a116 b i j*
        (Real.cos t*inner ℝ v (B4a39 b i j)+Real.sin t*inner ℝ v (B4a40 b i j))-‖v‖^2/2 := by
    funext t
    unfold B4a195 B4a13 SphereGeom.circlePt
    change inner ℝ v (B4a89 b i j+B4a116 b i j •
      (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j)-b.c i)-‖v‖^2/2 = _
    rw [show B4a89 b i j+B4a116 b i j •
      (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j)-b.c i =
      (B4a89 b i j-b.c i)+B4a116 b i j •
      (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j) by abel]
    simp only [inner_add_right,real_inner_smul_right]
  have hr : Real.sqrt (1-(dist (b.c i) (b.c (B4a94 b i j))/2)^2) = B4a116 b i j := by
    unfold B4a116 q
    congr 1
    ring
  have hT : SphereGeom.cross (B4a10 b i j) (B4a144 b i j-b.c i) =
      B4a116 b i j • B4a40 b i j := by
    have ht := B4a12 (B4a10 b i j) (B4a39 b i j)
      (dist (b.c i) (b.c (B4a94 b i j))/2) 0 (B4a50 b i j).aa (B4a50 b i j).ae1
    rw [← B4a40,← B4a20,B4a21] at ht
    simpa only [Gnomonic.capVelocity,Real.sin_zero,Real.cos_zero,neg_zero,zero_smul,
      one_smul,zero_add,hr] using ht.symm
  have hcos := (Real.hasDerivAt_cos (0:ℝ)).mul_const (inner ℝ v (B4a39 b i j))
  have hsin := (Real.hasDerivAt_sin (0:ℝ)).mul_const (inner ℝ v (B4a40 b i j))
  have hh := ((hasDerivAt_const (0:ℝ) (inner ℝ v (B4a89 b i j-b.c i))).add
    ((hcos.add hsin).const_mul (B4a116 b i j))).sub_const (‖v‖^2/2)
  have hd : HasDerivAt (B4a195 b i j ((j+1)+1))
      (inner ℝ (b.c (B4a94 b i ((j+1)+1))-b.c i)
        (SphereGeom.cross (B4a10 b i j) (B4a144 b i j-b.c i))) 0 := by
    rw [hfun,hT,real_inner_smul_right]
    simpa only [Pi.add_def,Pi.smul_def,Real.sin_zero,Real.cos_zero,neg_zero,
      zero_mul,one_mul,zero_add,add_zero] using hh
  have hstart := B4a201 b i j
  have hlt : B4a195 b i j ((j+1)+1) 0 < B4a195 b i j (j+1) 0 := by
    rw [hstart.2]; exact hstart.1
  have he : ∀ᶠ t in 𝓝 (0:ℝ), B4a195 b i j ((j+1)+1) t < B4a195 b i j (j+1) t :=
    (isOpen_lt (B4a197 b i j ((j+1)+1)) (B4a197 b i j (j+1))).mem_nhds hlt
  apply hd.congr_of_eventuallyEq
  filter_upwards [he] with t ht
  exact min_eq_right ht.le
private theorem AS4B.B4a156 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    (∀ t ∈ Set.Ioo 0 (B4a75 b i j), 0 < B4a174 b i j t) ∧
    (∀ t ∈ Set.Ioo (B4a75 b i j) (2*Real.pi), B4a174 b i j t < 0) := by
  obtain ⟨ε,hε,hplus,hminus⟩ := B4a166 (B4a174 b i j) _
    (B4a180 b i j) (B4a176 b i j)
    (B4a158 b i j)
  let δ := min ε (min (B4a75 b i j) (2*Real.pi-B4a75 b i j))/2
  have hδ : 0 < δ := half_pos (lt_min hε (lt_min (B4a79 b i j)
    (sub_pos.mpr (B4a77 b i j))))
  have hδε : δ < ε := by
    have hh := min_le_left ε (min (B4a75 b i j) (2*Real.pi-B4a75 b i j))
    dsimp only [δ] at hδ ⊢
    linarith
  have hδL : δ < B4a75 b i j := by
    have hh := (min_le_right ε (min (B4a75 b i j) (2*Real.pi-B4a75 b i j))).trans
      (min_le_left _ _)
    dsimp only [δ] at hδ ⊢
    linarith
  have hδC : δ < 2*Real.pi-B4a75 b i j := by
    have hh := (min_le_right ε (min (B4a75 b i j) (2*Real.pi-B4a75 b i j))).trans
      (min_le_right _ _)
    dsimp only [δ] at hδ ⊢
    linarith
  have hp := hplus δ hδ hδε
  have hn : B4a174 b i j (2*Real.pi-δ) < 0 := by
    have h := hminus (-δ) (by linarith) (neg_neg_of_pos hδ)
    have he := B4a179 b i j (-δ)
    have he' : -δ+2*Real.pi = 2*Real.pi-δ := by ring
    rw [he'] at he
    rwa [he]
  constructor
  · apply B4a200 (B4a174 b i j) (B4a175 b i j)
      0 (B4a75 b i j) δ ⟨hδ,hδL⟩ hp
    intro t ht hz
    rcases B4a181 b i j t ⟨ht.1.le,ht.2.trans (B4a77 b i j)⟩ hz with h | h
    · linarith [ht.1]
    · linarith [ht.2]
  · have hneg := B4a200 (fun t => -B4a174 b i j t)
      (B4a175 b i j).neg (B4a75 b i j) (2*Real.pi) (2*Real.pi-δ)
      ⟨by linarith,by linarith⟩ (neg_pos.mpr hn)
      (by
        intro t ht hz
        have hzero : B4a174 b i j t = 0 := neg_eq_zero.mp hz
        rcases B4a181 b i j t ⟨((B4a79 b i j).trans ht.1).le,ht.2⟩ hzero with h | h
        · linarith [ht.1,(B4a79 b i j)]
        · linarith [ht.1])
    intro t ht
    exact neg_pos.mp (hneg t ht)
private theorem AS4B.B4a162 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2*Real.pi)) :
    B4a13 b i j t ∈ Kset b.c ↔ t ≤ B4a75 b i j := by
  rw [← B4a178]
  constructor
  · intro h
    by_contra hn
    have hs := (B4a156 b i j).2 t ⟨lt_of_not_ge hn,ht.2⟩
    exact (not_lt_of_ge h) hs
  · intro h
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0,B4a180]
    · rcases eq_or_lt_of_le h with hL | hL
      · rw [hL,B4a177]
      · exact ((B4a156 b i j).1 t ⟨h0,hL⟩).le
private theorem AS4B.B4a155 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a13 b i j '' Set.Icc 0 (B4a75 b i j) =
      patch b.c i ∩ Metric.sphere (b.c (B4a94 b i j)) 1 := by
  ext p
  constructor
  · rintro ⟨t,ht,rfl⟩
    have hp := B4a18 b i j t
    exact ⟨⟨hp.1,(B4a162 b i j t ⟨ht.1,ht.2.trans_lt (B4a77 b i j)⟩).mpr ht.2⟩,hp.2⟩
  · rintro ⟨⟨hsi,hK⟩,hsj⟩
    have hperp : ∀ a : Fin 2,
        inner ℝ (b.c (B4a94 b i j)-b.c i) (![B4a39 b i j,B4a40 b i j] a) = 0 := by
      have F := B4a50 b i j
      have hdz : (dist (b.c i) (b.c (B4a94 b i j)))⁻¹ ≠ 0 :=
        inv_ne_zero (ne_of_gt (B4a38 b i j).1)
      intro a
      fin_cases a
      · have he := F.ae1
        simp only [B4a10,real_inner_smul_left] at he
        simpa using (mul_eq_zero.mp he).resolve_left hdz
      · have he := F.ae2
        simp only [B4a10,real_inner_smul_left] at he
        simpa using (mul_eq_zero.mp he).resolve_left hdz
    have hchart := CircleArc.pair_sphere_chart_two (b.c i) (b.c (B4a94 b i j))
      ![B4a39 b i j,B4a40 b i j] (B4a52 b i j) hperp
      (B4a38 b i j).1 (B4a38 b i j).2
    have hmem : p ∈ Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1 := ⟨hsi,hsj⟩
    rw [hchart] at hmem
    change ∃ t ∈ Set.Icc 0 (2*Real.pi), B4a13 b i j t = p at hmem
    obtain ⟨t,ht,he⟩ := hmem
    rcases eq_or_lt_of_le ht.2 with hT | hT
    · refine ⟨0,⟨le_rfl,(B4a79 b i j).le⟩,?_⟩
      rw [hT] at he
      have hc : B4a13 b i j (2*Real.pi) = B4a13 b i j 0 := by
        simpa only [zero_add] using B4a163 b i j 0
      exact hc.symm.trans he
    · refine ⟨t,⟨ht.1,?_⟩,he⟩
      exact (B4a162 b i j t ⟨ht.1,hT⟩).mp (by rwa [he])
private theorem AS4B.B4a160 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ioo 0 (B4a75 b i j)) (m : Fin 4) (hmi : m ≠ i)
    (hmj : m ≠ B4a94 b i j) : dist (B4a13 b i j t) (b.c m) < 1 := by
  have hp : B4a13 b i j t ∈ patch b.c i ∩ Metric.sphere (b.c (B4a94 b i j)) 1 := by
    rw [← B4a155]
    exact ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hk := hp.1.2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
  apply lt_of_le_of_ne (hk m)
  intro he
  rcases B4a199 b i j t ⟨ht.1.le,ht.2.trans (B4a77 b i j)⟩
    hp.1.2 m hmi hmj he with h | h
  · linarith [ht.1]
  · linarith [ht.2]
private theorem AS4B.B4a159 (b : B4a0) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (B4a75 b i j)) : B4a13 b i j t ∈ patch b.c i := by
  have hp : B4a13 b i j t ∈ patch b.c i ∩ Metric.sphere (b.c (B4a94 b i j)) 1 := by
    rw [← B4a155]
    exact ⟨t,ht,rfl⟩
  exact hp.1
private theorem AS4B.B4a169 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a55 b i j '' Set.Icc 0 (B4a75 b i j) =
      B4a108 b i '' (patch b.c i ∩ Metric.sphere (b.c (B4a94 b i j)) 1) := by
  ext y
  constructor
  · rintro ⟨t,ht,rfl⟩
    have hp := B4a159 b i j t ht
    refine ⟨B4a13 b i j t,⟨hp,(B4a18 b i j t).2⟩,?_⟩
    rw [B4a59 b i j t hp]
    rfl
  · rintro ⟨p,hp,rfl⟩
    rw [← B4a155] at hp
    obtain ⟨t,ht,he⟩ := hp
    refine ⟨t,ht,?_⟩
    rw [B4a59 b i j t (B4a159 b i j t ht)]
    change B4a108 b i (B4a13 b i j t) = B4a108 b i p
    rw [he]
private theorem AS4B.B4a171 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a55 b i j (B4a75 b i j) = B4a55 b i (j+1) 0 := by
  rw [B4a59 b i j _
      (B4a159 b i j _ ⟨(B4a79 b i j).le,le_rfl⟩),
    B4a59 b i (j+1) _
      (B4a159 b i (j+1) _ ⟨le_rfl,(B4a79 b i (j+1)).le⟩)]
  change B4a108 b i (B4a13 b i j (B4a75 b i j)) =
    B4a108 b i (B4a13 b i (j+1) 0)
  rw [B4a15]
private theorem AS4B.B4a173 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    Set.InjOn (B4a55 b i j) (Set.Ico 0 (B4a75 b i j)) := by
  intro t ht u hu he
  have htpatch := B4a159 b i j t ⟨ht.1,ht.2.le⟩
  have hupatch := B4a159 b i j u ⟨hu.1,hu.2.le⟩
  rw [B4a59 b i j t htpatch,
    B4a59 b i j u hupatch] at he
  have hc : B4a13 b i j t = B4a13 b i j u := B4a112 b i htpatch hupatch he
  exact B4a161 b i j ⟨ht.1,ht.2.trans (B4a77 b i j)⟩
    ⟨hu.1,hu.2.trans (B4a77 b i j)⟩ hc
private theorem AS4B.B4a172 (b : B4a0) (i : Fin 4) (j k : Fin 3) (hjk : j ≠ k) :
    Disjoint (B4a55 b i j '' Set.Ioo 0 (B4a75 b i j))
      (B4a55 b i k '' Set.Ioo 0 (B4a75 b i k)) := by
  apply Set.disjoint_left.mpr
  intro y hyj hyk
  obtain ⟨t,ht,he⟩ := hyj
  obtain ⟨u,hu,hf⟩ := hyk
  have htpatch := B4a159 b i j t ⟨ht.1.le,ht.2.le⟩
  have hupatch := B4a159 b i k u ⟨hu.1.le,hu.2.le⟩
  have heq := he.trans hf.symm
  rw [B4a59 b i j t htpatch,
    B4a59 b i k u hupatch] at heq
  have hp : B4a13 b i j t = B4a13 b i k u := B4a112 b i htpatch hupatch heq
  have hlt := B4a160 b i j t ht (B4a94 b i k) (B4a97 b i k)
    (fun he => hjk (B4a96 b i he).symm)
  rw [hp,(B4a18 b i k u).2] at hlt
  exact lt_irrefl _ hlt
private theorem AS4B.B4a170 (b : B4a0) (i : Fin 4) :
    (⋃ j : Fin 3, B4a55 b i j '' Set.Icc 0 (B4a75 b i j)) = frontier (B4a1 b i) := by
  rw [B4a7]
  apply Set.iUnion_congr
  intro j
  exact B4a169 b i j
private def AS4B.B4a188 (b : B4a0) (i : Fin 4) : PositiveConvexBoundary where
  n := 2
  D := B4a1 b i
  gamma := B4a55 b i
  len := B4a75 b i
  compact := B4a3 b i
  convex := B4a4 b i
  interior_nonempty := B4a8 b i
  len_pos := B4a79 b i
  smooth := B4a56 b i
  regular := fun j t ht => B4a62 b i j t (B4a159 b i j t ht)
  cyclic := B4a171 b i
  injective := B4a173 b i
  disjoint_arcs := B4a172 b i
  boundary := B4a170 b i
  left := fun j t ht x hx => B4a61 b i j t
    (B4a159 b i j t ⟨ht.1.le,ht.2.le⟩) x hx
@[simp] private theorem B4a190 (b : B4a0) (i : Fin 4) :
    (B4a188 b i).D = B4a1 b i := rfl
@[simp] private theorem B4a189 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    (B4a188 b i).gamma j = B4a55 b i j := rfl
@[simp] private theorem B4a191 (b : B4a0) (i : Fin 4) (j : Fin 3) :
    (B4a188 b i).len j = B4a75 b i j := rfl
@[simp] private theorem B4a192 (b : B4a0) (i : Fin 4) :
    (B4a188 b i).n = 2 := rfl
end AS4Scope18
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope19
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2)
private theorem AS4B.B4a35 (e f n:Pt) (A B C D E F:ℝ) :
    SphereGeom.cross (A • e+B • f+C • n) (D • e+E • f+F • n) =
      (A*E-B*D) • SphereGeom.cross e f+(B*F-C*E) • SphereGeom.cross f n+(C*D-A*F) • SphereGeom.cross n e:=by
  ext k;fin_cases k <;>simp [HardSphereB5.Lean.Geometry.PathCore.cross,SphereGeom.cross,crossProduct]<;>ring
private theorem AS4B.B4a32 (b:B4a0) (i:Fin 4) :
    SphereGeom.cross (B4a39 b i 0) (B4a40 b i 0)=B4a10 b i 0 ∧
    SphereGeom.cross (B4a40 b i 0) (B4a10 b i 0)=B4a39 b i 0 := by
  have F:=B4a50 b i 0
  have hvn:inner ℝ (B4a39 b i 0) (B4a10 b i 0)=0:=by
    rw [real_inner_comm];exact F.ae1
  constructor
  · change SphereGeom.cross (B4a39 b i 0) (SphereGeom.cross (B4a10 b i 0) (B4a39 b i 0))=B4a10 b i 0
    change SphereGeom.cross (B4a39 b i 0) (SphereGeom.cross (B4a10 b i 0) (B4a39 b i 0))=B4a10 b i 0
    rw [SphereGeom.cross_vec_triple,F.e11,F.ae1]
    simp only [one_smul,zero_smul,sub_zero]
  · have hs:SphereGeom.cross (B4a40 b i 0) (B4a10 b i 0)=-SphereGeom.cross (B4a10 b i 0) (B4a40 b i 0):=by
      ext k;fin_cases k <;>simp [HardSphereB5.Lean.Geometry.PathCore.cross,SphereGeom.cross,crossProduct]<;>ring
    rw [hs]
    change -SphereGeom.cross (B4a10 b i 0) (SphereGeom.cross (B4a10 b i 0) (B4a39 b i 0))=B4a39 b i 0
    change -SphereGeom.cross (B4a10 b i 0) (SphereGeom.cross (B4a10 b i 0) (B4a39 b i 0))=B4a39 b i 0
    rw [SphereGeom.cross_vec_triple,F.ae1,F.aa]
    simp only [zero_smul,one_smul,zero_sub,neg_neg]
private theorem AS4B.B4a136 (b:B4a0) (i:Fin 4) (u v:Pt) :
    (B4a133 b i).symm (SphereGeom.cross u v)=
      SphereGeom.cross ((B4a133 b i).symm u) ((B4a133 b i).symm v) := by
  have hu:=B4a51 b i u
  have hv:=B4a51 b i v
  have hcross:SphereGeom.cross u v=
      (inner ℝ (B4a39 b i 0) u*inner ℝ (B4a40 b i 0) v-
       inner ℝ (B4a40 b i 0) u*inner ℝ (B4a39 b i 0) v) • B4a10 b i 0+
      (inner ℝ (B4a40 b i 0) u*inner ℝ (B4a10 b i 0) v-
       inner ℝ (B4a10 b i 0) u*inner ℝ (B4a40 b i 0) v) • B4a39 b i 0+
      (inner ℝ (B4a10 b i 0) u*inner ℝ (B4a39 b i 0) v-
       inner ℝ (B4a39 b i 0) u*inner ℝ (B4a10 b i 0) v) • B4a40 b i 0:=by
    calc
      _=SphereGeom.cross (inner ℝ (B4a39 b i 0) u • B4a39 b i 0+
        inner ℝ (B4a40 b i 0) u • B4a40 b i 0+
        inner ℝ (B4a10 b i 0) u • B4a10 b i 0)
        (inner ℝ (B4a39 b i 0) v • B4a39 b i 0+
        inner ℝ (B4a40 b i 0) v • B4a40 b i 0+
        inner ℝ (B4a10 b i 0) v • B4a10 b i 0):=by rw [hu,hv]
      _=_:=by
        rw [B4a35,(B4a32 b i).1,(B4a32 b i).2]
        rfl
  rw [B4a134,B4a134,B4a134,hcross]
  have F:=B4a50 b i 0
  have h01:inner ℝ (B4a40 b i 0) (B4a39 b i 0)=0:=by rw [real_inner_comm];exact F.e12
  have h02:inner ℝ (B4a39 b i 0) (B4a10 b i 0)=0:=by rw [real_inner_comm];exact F.ae1
  have h12:inner ℝ (B4a40 b i 0) (B4a10 b i 0)=0:=by rw [real_inner_comm];exact F.ae2
  ext k;fin_cases k <;>
    simp [HardSphereB5.Lean.Geometry.PathCore.cross,SphereGeom.cross,crossProduct,inner_add_right,real_inner_smul_right,F.aa,F.ae1,F.ae2,
      F.e11,F.e22,F.e12,h01,h02,h12] <;>
      simp only [←real_inner_self_eq_norm_sq,F.aa,F.e11,F.e22,mul_one]
private theorem AS4B.B4a132 (b:B4a0) (i:Fin 4) (j:Fin 3) (t:ℝ) :
    (B4a133 b i).symm (B4a13 b i j t-b.c i)=
      Gnomonic.capArc ((B4a133 b i).symm (B4a10 b i j))
        ((B4a133 b i).symm (B4a39 b i j))
        (SphereGeom.cross ((B4a133 b i).symm (B4a10 b i j))
          ((B4a133 b i).symm (B4a39 b i j))) (B4a63 b i j) t := by
  rw [B4a20]
  unfold Gnomonic.capArc
  simp only [map_add,map_smul]
  rw [←B4a136]
  rfl
private theorem AS4B.B4a69 (b:B4a0) (i:Fin 4) (j:Fin 3)
    (t:ℝ) (hp:B4a13 b i j t∈patch b.c i) :
    (fun s=>Gnomonic.inverseNorth (B4a55 b i j s)) =ᶠ[nhds t]
      Gnomonic.capArc ((B4a133 b i).symm (B4a10 b i j))
        ((B4a133 b i).symm (B4a39 b i j))
        (SphereGeom.cross ((B4a133 b i).symm (B4a10 b i j))
          ((B4a133 b i).symm (B4a39 b i j))) (B4a63 b i j) := by
  have H:=B4a60 b i j t hp
  let δ:=B4a46 b i
  have hc:Continuous (fun s=>inner ℝ (B4a10 b i 0) (B4a13 b i j s-b.c i)):=
    continuous_const.inner ((B4a19 b i j).continuous.sub continuous_const)
  have hn:IsOpen {s:ℝ|0 < inner ℝ (B4a10 b i 0) (B4a13 b i j s-b.c i)}:=
    isOpen_lt continuous_const hc
  have ht:=B4a106 b i _ hp
  filter_upwards [H,hn.mem_nhds ht] with s hs hpos
  rw [hs]
  have hu:‖B4a13 b i j s-b.c i‖=1:=by
    simpa only [Metric.mem_sphere,dist_eq_norm] using (B4a18 b i j s).1
  have he:B4a68 b i (B4a54 b i j s)=B4a13 b i j s-b.c i:=by
    rw [B4a68,B4a54,B4a88 b i _ hpos.ne',norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),hu,mul_one,inv_inv,
      ←mul_smul,mul_inv_cancel₀ hpos.ne',one_smul]
  have hr:B4a68 b i (B4a54 b i j s)=B4a133 b i (Gnomonic.inverseNorth (B4a54 b i j s)):=by
    rw [B4a71]
    unfold Gnomonic.inverseFrame Gnomonic.inverseNorth Gnomonic.northRadius
    congr 1
    ext k
    fin_cases k <;> simp [Gnomonic.northLift,Gnomonic.northPlaneInclusion,Gnomonic.north,
      EuclideanSpace.inner_single_left]
  have hh: Gnomonic.inverseNorth (B4a54 b i j s)=(B4a133 b i).symm (B4a13 b i j s-b.c i):=by
    rw [←he,hr,(B4a133 b i).symm_apply_apply]
  rw [hh]
  exact B4a132 b i j s
end AS4Scope19
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
private def SolidGeom.CapPolar.rayGauge (a h t : ℝ) : ℝ := (h-a*Real.cos t)/Real.sin t
private lemma SolidGeom.CapPolar.rayGauge_hasDerivAt (a h t : ℝ) (ht : t ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt (SolidGeom.CapPolar.rayGauge a h)
      ((a-h*Real.cos t)/(Real.sin t)^2) t := by
  have hs : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  have hd := ((hasDerivAt_const t h).sub ((Real.hasDerivAt_cos t).const_mul a)).div
    (Real.hasDerivAt_sin t) hs
  have he : (((0-a*(-Real.sin t))*Real.sin t-(h-a*Real.cos t)*Real.cos t)/(Real.sin t)^2) =
      (a-h*Real.cos t)/(Real.sin t)^2 := by
    congr 1
    have hc := Real.sin_sq_add_cos_sq t
    linear_combination a*hc
  have hf : (((fun x : ℝ => h)-(fun y => a*Real.cos y))/Real.sin) =
      SolidGeom.CapPolar.rayGauge a h := rfl
  simpa only [hf,Pi.sub_apply,he] using hd
private lemma SolidGeom.CapPolar.rayGauge_strictMono (a h : ℝ) (hh : 0 < h) (ha : h < a) :
    StrictMonoOn (SolidGeom.CapPolar.rayGauge a h) (Set.Ioo 0 Real.pi) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) Real.pi)
  · exact ((continuous_const.sub (continuous_const.mul Real.continuous_cos)).continuousOn).div
      Real.continuous_sin.continuousOn (fun t ht => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(SolidGeom.CapPolar.rayGauge_hasDerivAt a h t ht).deriv]
    apply div_pos
    · have hc := Real.cos_le_one t
      nlinarith
    · exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
private lemma SolidGeom.CapPolar.ray_cap_iff (a b h ρ t : ℝ) (hh : 0 < h) (ha : h < a)
    (hρ : ρ ∈ Set.Ioo 0 Real.pi) (hroot : a*Real.cos ρ+b*Real.sin ρ=h)
    (ht : t ∈ Set.Icc 0 Real.pi) : h ≤ a*Real.cos t+b*Real.sin t ↔ t ≤ ρ := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0,Real.cos_zero,Real.sin_zero]
    simp only [mul_one,mul_zero,add_zero]
    exact iff_of_true ha.le hρ.1.le
  rcases eq_or_lt_of_le ht.2 with hπ | hπ
  · rw [hπ,Real.cos_pi,Real.sin_pi]
    constructor <;> intro h <;> nlinarith [hρ.2]
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hsinρ := Real.sin_pos_of_pos_of_lt_pi hρ.1 hρ.2
  have hr : SolidGeom.CapPolar.rayGauge a h ρ = b := by
    unfold SolidGeom.CapPolar.rayGauge
    apply (div_eq_iff (ne_of_gt hsinρ)).mpr
    linarith
  have hmono := SolidGeom.CapPolar.rayGauge_strictMono a h hh ha
  have hle : SolidGeom.CapPolar.rayGauge a h t ≤ b ↔ t ≤ ρ := by
    rw [← hr]
    exact hmono.le_iff_le ⟨h0,hπ⟩ hρ
  rw [← hle]
  unfold SolidGeom.CapPolar.rayGauge
  rw [div_le_iff₀ hsin]
  constructor <;> intro h <;> linarith
private lemma SolidGeom.CapPolar.polar_norm (e : Fin 3 → E3) (he : Orthonormal ℝ e) (t φ : ℝ) :
    ‖SolidGeom.CapPolar.polar e t φ‖ = 1 := by
  have hinner := orthonormal_iff_ite.mp he
  have hsq : ‖SolidGeom.CapPolar.polar e t φ‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold SolidGeom.CapPolar.polar
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,hinner]
    simp
    linear_combination (Real.sin t)^2*(Real.sin_sq_add_cos_sq φ)+(Real.sin_sq_add_cos_sq t)
  nlinarith [norm_nonneg (SolidGeom.CapPolar.polar e t φ)]
private lemma SolidGeom.CapPolar.winner_min (P : Profile) (φ : ℝ) :
    ∀ j : Fin 3, SolidGeom.CapPolar.radius P φ ≤ P.rho j φ := by
  unfold SolidGeom.CapPolar.radius SolidGeom.CapPolar.winner
  split_ifs with h0 h1
  · intro j
    fin_cases j
    · exact le_rfl
    · exact h0.1
    · exact h0.2
  · intro j
    fin_cases j
    · by_contra hn
      exact h0 ⟨(lt_of_not_ge hn).le,((lt_of_not_ge hn).le.trans h1)⟩
    · exact le_rfl
    · exact h1
  · have h21 : P.rho 2 φ ≤ P.rho 1 φ := (le_of_not_ge h1)
    intro j
    fin_cases j
    · by_contra hn
      exact h0 ⟨(lt_of_not_ge hn).le.trans h21,(lt_of_not_ge hn).le⟩
    · exact h21
    · exact le_rfl
private lemma SolidGeom.CapPolar.ray_membership (P : Profile) (t φ : ℝ)
    (ht : t ∈ Set.Icc 0 Real.pi) :
    SolidGeom.CapPolar.polar P.e t φ ∈ SolidGeom.CapPolar.caps P ↔
      t ≤ SolidGeom.CapPolar.radius P φ := by
  have hcap : ∀ j, P.height j ≤ inner ℝ (P.normal j) (SolidGeom.CapPolar.polar P.e t φ) ↔
      t ≤ P.rho j φ := by
    intro j
    let a := inner ℝ (P.normal j) (P.e 2)
    let b := Real.cos φ*inner ℝ (P.normal j) (P.e 0)+Real.sin φ*inner ℝ (P.normal j) (P.e 1)
    have hroot : a*Real.cos (P.rho j φ)+b*Real.sin (P.rho j φ)=P.height j := by
      have hr := P.ray_boundary j φ
      unfold SolidGeom.CapPolar.polar at hr
      simp only [inner_add_right,real_inner_smul_right] at hr
      dsimp [a,b]
      nlinarith [hr]
    have he := SolidGeom.CapPolar.ray_cap_iff a b (P.height j) (P.rho j φ) t
      (P.height_pos j) (P.pole_inside j) (P.rho_range j φ) hroot ht
    unfold SolidGeom.CapPolar.polar
    simp only [inner_add_right,real_inner_smul_right]
    convert he using 1 <;> dsimp [a,b] <;> ring
  simp only [SolidGeom.CapPolar.caps,Set.mem_setOf_eq,SolidGeom.CapPolar.polar_norm P.e P.frame,
    true_and,hcap]
  constructor
  · intro h
    exact h (SolidGeom.CapPolar.winner P φ)
  · intro h j
    exact h.trans (SolidGeom.CapPolar.winner_min P φ j)
private lemma SolidGeom.CapPolar.caps_measurable (P : Profile) : MeasurableSet (SolidGeom.CapPolar.caps P) := by
  have hc : IsClosed (SolidGeom.CapPolar.caps P) := by
    have he : SolidGeom.CapPolar.caps P = {u : E3 | ‖u‖=1} ∩ ⋂ j, {u | P.height j ≤ inner ℝ (P.normal j) u} := by
      ext u
      simp [SolidGeom.CapPolar.caps]
    rw [he]
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop))
  exact hc.measurableSet
private lemma SolidGeom.CapPolar.winner_measurable (P : Profile) : Measurable (SolidGeom.CapPolar.winner P) := by
  unfold SolidGeom.CapPolar.winner
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 1).measurable).inter
      (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 2).measurable)
  · exact measurableSet_le (P.rho_continuous 1).measurable (P.rho_continuous 2).measurable
private lemma SolidGeom.CapPolar.sector_measurable (P : Profile) (j : Fin 3) :
    MeasurableSet (SolidGeom.CapPolar.sector P j) :=
  measurableSet_Icc.inter ((SolidGeom.CapPolar.winner_measurable P)
    (MeasurableSet.singleton j))
private lemma SolidGeom.CapPolar.polar_coordinates (P : Profile) (t φ : ℝ) :
    inner ℝ (P.e 0) (polar P.e t φ) = Real.sin t*Real.cos φ ∧
    inner ℝ (P.e 1) (polar P.e t φ) = Real.sin t*Real.sin φ ∧
    inner ℝ (P.e 2) (polar P.e t φ) = Real.cos t := by
  have he := orthonormal_iff_ite.mp P.frame
  have h00 : inner ℝ (P.e (0:Fin 3)) (P.e (0:Fin 3)) = 1 := by
    rw [he]
    exact if_pos rfl
  have h01 : inner ℝ (P.e (0:Fin 3)) (P.e (1:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (0:Fin 3) ≠ 1)
  have h02 : inner ℝ (P.e (0:Fin 3)) (P.e (2:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (0:Fin 3) ≠ 2)
  have h10 : inner ℝ (P.e (1:Fin 3)) (P.e (0:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (1:Fin 3) ≠ 0)
  have h11 : inner ℝ (P.e (1:Fin 3)) (P.e (1:Fin 3)) = 1 := by
    rw [he]
    exact if_pos rfl
  have h12 : inner ℝ (P.e (1:Fin 3)) (P.e (2:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (1:Fin 3) ≠ 2)
  have h20 : inner ℝ (P.e (2:Fin 3)) (P.e (0:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (2:Fin 3) ≠ 0)
  have h21 : inner ℝ (P.e (2:Fin 3)) (P.e (1:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (2:Fin 3) ≠ 1)
  have h22 : inner ℝ (P.e (2:Fin 3)) (P.e (2:Fin 3)) = 1 := by
    rw [he]
    exact if_pos rfl
  simp only [polar,inner_add_right,real_inner_smul_right,h00,h01,h02,h10,h11,h12,h20,h21,h22,mul_one,mul_zero,add_zero,zero_add]
  trivial
private lemma SolidGeom.CapPolar.exitPoint_mem (P : Profile) (φ : ℝ) : exitPoint P φ ∈ caps P := by
  apply (ray_membership P (radius P φ) φ
    ⟨(P.rho_range _ φ).1.le,(P.rho_range _ φ).2.le⟩).mpr
  exact le_rfl
private lemma SolidGeom.CapPolar.ray_equal_root (a b h r t : ℝ) (hh : 0 < h) (ha : h < a)
    (hr : r ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hroot : a*Real.cos r+b*Real.sin r=h) :
    a*Real.cos t+b*Real.sin t=h ↔ t=r := by
  have hrG : rayGauge a h r = b := by
    unfold rayGauge
    apply (div_eq_iff (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2))).mpr
    linarith
  constructor
  · intro he
    have htG : rayGauge a h t = b := by
      unfold rayGauge
      apply (div_eq_iff (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))).mpr
      linarith
    exact (rayGauge_strictMono a h hh ha).injOn ht hr (htG.trans hrG.symm)
  · rintro rfl
    exact hroot
private lemma SolidGeom.CapPolar.active_exit_proof (P : Profile) (j : Fin 3) (φ : ℝ) :
    P.rho j φ = radius P φ ↔ P.height j = inner ℝ (P.normal j) (exitPoint P φ) := by
  let a := inner ℝ (P.normal j) (P.e 2)
  let b := Real.cos φ*inner ℝ (P.normal j) (P.e 0)+Real.sin φ*inner ℝ (P.normal j) (P.e 1)
  have hexp : ∀ t : ℝ, inner ℝ (P.normal j) (polar P.e t φ) = a*Real.cos t+b*Real.sin t := by
    intro t
    unfold polar
    simp only [inner_add_right,real_inner_smul_right]
    dsimp [a,b]
    ring
  have hroot : a*Real.cos (P.rho j φ)+b*Real.sin (P.rho j φ)=P.height j := by
    rw [← hexp]
    exact P.ray_boundary j φ
  have he := ray_equal_root a b (P.height j) (P.rho j φ) (radius P φ)
    (P.height_pos j) (P.pole_inside j) (P.rho_range j φ) (P.rho_range _ φ) hroot
  unfold exitPoint
  rw [hexp]
  exact ⟨fun h => (he.mpr h.symm).symm, fun h => (he.mp h.symm).symm⟩
private lemma SolidGeom.CapPolar.polar_azimuth_inj (P : Profile) (r s φ ψ : ℝ)
    (hr : r ∈ Set.Ioo 0 Real.pi) (hs : s ∈ Set.Ioo 0 Real.pi)
    (hφ : φ ∈ Set.Ico 0 (2*Real.pi)) (hψ : ψ ∈ Set.Ico 0 (2*Real.pi))
    (he : polar P.e r φ = polar P.e s ψ) : φ=ψ := by
  have hc0 := congrArg (fun u => inner ℝ (P.e 0) u) he
  have hc1 := congrArg (fun u => inner ℝ (P.e 1) u) he
  have hc2 := congrArg (fun u => inner ℝ (P.e 2) u) he
  rw [(polar_coordinates P r φ).1,(polar_coordinates P s ψ).1] at hc0
  rw [(polar_coordinates P r φ).2.1,(polar_coordinates P s ψ).2.1] at hc1
  rw [(polar_coordinates P r φ).2.2,(polar_coordinates P s ψ).2.2] at hc2
  have hrs : r=s := Real.injOn_cos ⟨hr.1.le,hr.2.le⟩ ⟨hs.1.le,hs.2.le⟩ hc2
  subst s
  have hz := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2)
  have hcos := (mul_left_cancel₀ hz hc0)
  have hsin := (mul_left_cancel₀ hz hc1)
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hcos hsin)
  have hkm : (-1:ℝ)<(k:ℝ) := by nlinarith [hφ.1,hφ.2,hψ.1,hψ.2,Real.pi_pos]
  have hkp : (k:ℝ)<(1:ℝ) := by nlinarith [hφ.1,hφ.2,hψ.1,hψ.2,Real.pi_pos]
  have hm : (-1:ℤ)<k := by exact_mod_cast hkm
  have hp : k<(1:ℤ) := by exact_mod_cast hkp
  have hzero : k=0 := by omega
  rw [hzero] at hk
  simpa only [Int.cast_zero,mul_zero,sub_eq_zero] using hk
private lemma SolidGeom.CapPolar.exitPoint_inj_proof (P : Profile) :
    Set.InjOn (exitPoint P) (Set.Ico 0 (2*Real.pi)) := by
  intro φ hφ ψ hψ he
  exact polar_azimuth_inj P (radius P φ) (radius P ψ) φ ψ
    (P.rho_range _ φ) (P.rho_range _ ψ) hφ hψ he
open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore AS4P
private lemma SolidGeom.CapPolar.matching_dist_pos {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) : 0 < dist (c i) (c (o j)) := by
  have hh := P.height_pos j
  rw [hm.height_eq j] at hh
  linarith
private lemma SolidGeom.CapPolar.matching_labels {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (m : Fin 4) : m=i ∨ ∃ j : Fin 3, m=o j := by
  have hcover : ∀ i a b d m : Fin 4, a ≠ i → b ≠ i → d ≠ i → a ≠ b → a ≠ d → b ≠ d →
      m=i ∨ m=a ∨ m=b ∨ m=d := by decide
  have hc := hcover i (o 0) (o 1) (o 2) m (hm.label_ne 0) (hm.label_ne 1) (hm.label_ne 2)
    (fun h => (by decide : (0:Fin 3) ≠ 1) (hm.label_injective h))
    (fun h => (by decide : (0:Fin 3) ≠ 2) (hm.label_injective h))
    (fun h => (by decide : (1:Fin 3) ≠ 2) (hm.label_injective h))
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨0,h⟩
  · exact Or.inr ⟨1,h⟩
  · exact Or.inr ⟨2,h⟩
private lemma SolidGeom.CapPolar.matching_inner_ball {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) (u : E3) (hu : ‖u‖=1) :
    P.height j ≤ inner ℝ (P.normal j) u ↔ c i+u ∈ Metric.closedBall (c (o j)) 1 := by
  let d := dist (c i) (c (o j))
  let v := c (o j)-c i
  have hd := matching_dist_pos hm j
  have hn : ‖v‖^2=d^2 := by dsimp [v,d];rw [← dist_eq_norm,dist_comm]
  have hv : c i+u-c (o j) = u-v := by dsimp [v];abel
  have hsq : dist (c i+u) (c (o j))^2 = 1-2*inner ℝ v u+d^2 := by
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,hn]
    rw [real_inner_comm]
    ring
  rw [hm.height_eq j,hm.normal_eq j,real_inner_smul_left]
  change d/2 ≤ d⁻¹*inner ℝ v u ↔ dist (c i+u) (c (o j)) ≤ 1
  have he : d/2 ≤ d⁻¹*inner ℝ v u ↔ d^2/2 ≤ inner ℝ v u := by
    rw [show d⁻¹*inner ℝ v u = inner ℝ v u/d by ring,le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor <;> intro h <;> nlinarith [dist_nonneg (x:=c i+u) (y:=c (o j))]
private lemma SolidGeom.CapPolar.matching_inner_sphere {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) (u : E3) (hu : ‖u‖=1) :
    P.height j = inner ℝ (P.normal j) u ↔ dist (c i+u) (c (o j))=1 := by
  let d := dist (c i) (c (o j))
  let v := c (o j)-c i
  have hd := matching_dist_pos hm j
  have hn : ‖v‖^2=d^2 := by dsimp [v,d];rw [← dist_eq_norm,dist_comm]
  have hv : c i+u-c (o j) = u-v := by dsimp [v];abel
  have hsq : dist (c i+u) (c (o j))^2 = 1-2*inner ℝ v u+d^2 := by
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,hn]
    rw [real_inner_comm]
    ring
  rw [hm.height_eq j,hm.normal_eq j,real_inner_smul_left]
  change d/2 = d⁻¹*inner ℝ v u ↔ dist (c i+u) (c (o j)) = 1
  have he : d/2 = d⁻¹*inner ℝ v u ↔ d^2/2 = inner ℝ v u := by
    rw [show d⁻¹*inner ℝ v u = inner ℝ v u/d by ring,eq_div_iff (ne_of_gt hd)]
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor <;> intro h <;> nlinarith [dist_nonneg (x:=c i+u) (y:=c (o j))]
private lemma SolidGeom.CapPolar.matching_patch_iff {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (u : E3) : u ∈ caps P ↔ c i+u ∈ patch c i := by
  constructor
  · rintro ⟨hu,hcaps⟩
    constructor
    · simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hu
    · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
      intro m
      rcases matching_labels hm m with hmi | ⟨j,hmj⟩
      · rw [hmi]
        change dist (c i+u) (c i) ≤ 1
        simpa only [dist_eq_norm,add_sub_cancel_left,hu] using (le_rfl : (1:ℝ) ≤ 1)
      · rw [hmj]
        exact (matching_inner_ball hm j u hu).mp (hcaps j)
  · rintro ⟨hsi,hK⟩
    have hu : ‖u‖=1 := by simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hsi
    refine ⟨hu,?_⟩
    intro j
    apply (matching_inner_ball hm j u hu).mpr
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hK
    exact hK _
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore AS4P
open scoped RealInnerProductSpace
section AS4Scope20
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
private theorem AS4B.AA_active_parameter (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) (φ : ℝ)
    (hφ : φ ∈ Set.Icc 0 (2*Real.pi)) :
    φ ∈ activeAzimuth P j ↔ ∃! t : ℝ,
      t ∈ Set.Icc 0 (B4a75 b i j) ∧ B4a13 b i j t=b.c i+exitPoint P φ := by
  constructor
  · intro ha
    have hu := exitPoint_mem P φ
    have hx : b.c i+exitPoint P φ ∈ patch b.c i ∩ Metric.sphere (b.c (B4a94 b i j)) 1 :=
      ⟨(matching_patch_iff hm _).mp hu,
        (matching_inner_sphere hm j _ hu.1).mp ((active_exit_proof P j φ).mp ha.2)⟩
    rw [← B4a155] at hx
    obtain ⟨t,ht,he⟩ := hx
    refine ⟨t,⟨ht,he⟩,?_⟩
    intro s hs
    exact B4a161 b i j
      ⟨hs.1.1,hs.1.2.trans_lt (B4a77 b i j)⟩
      ⟨ht.1,ht.2.trans_lt (B4a77 b i j)⟩ (hs.2.trans he.symm)
  · rintro ⟨t,⟨ht,he⟩,_⟩
    have hs : dist (b.c i+exitPoint P φ) (b.c (B4a94 b i j))=1 := by
      rw [← he]
      exact (B4a18 b i j t).2
    exact ⟨hφ,(active_exit_proof P j φ).mpr ((matching_inner_sphere hm j _ (exitPoint_mem P φ).1).mpr hs)⟩
private theorem AS4B.AA_tie_parameter_endpoints (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) (φ t : ℝ)
    (hφ : φ ∈ Set.Icc 0 (2*Real.pi)) (ht : t ∈ Set.Icc 0 (B4a75 b i j))
    (he : B4a13 b i j t=b.c i+exitPoint P φ) :
    φ ∈ tieAzimuth P ↔ t=0 ∨ t=B4a75 b i j := by
  have hu := exitPoint_mem P φ
  have hact : ∀ k : Fin 3, P.rho k φ=radius P φ ↔
      dist (B4a13 b i j t) (b.c (B4a94 b i k))=1 := by
    intro k
    rw [he]
    exact (active_exit_proof P k φ).trans (matching_inner_sphere hm k _ hu.1)
  constructor
  · rintro ⟨_,a,d,had,ha,hd⟩
    have hex : ∃ k : Fin 3, k ≠ j ∧ P.rho k φ=radius P φ := by
      by_cases haj : a=j
      · exact ⟨d,fun h => had (haj.trans h.symm),hd⟩
      · exact ⟨a,haj,ha⟩
    obtain ⟨k,hkj,hk⟩ := hex
    exact B4a199 b i j t
      ⟨ht.1,ht.2.trans_lt (B4a77 b i j)⟩
      (B4a159 b i j t ht).2 (B4a94 b i k) (B4a97 b i k)
      (fun h => hkj (B4a96 b i h)) ((hact k).mp hk)
  · intro htend
    have hj : P.rho j φ=radius P φ := (hact j).mpr (B4a18 b i j t).2
    rcases htend with h0 | hL
    · have hk : dist (B4a13 b i j t) (b.c (B4a94 b i ((j+1)+1)))=1 := by
        rw [h0,B4a21]
        exact (B4a153 b (B4a94 b i (j+1))).1 _
          (fun h => B4a187 j (B4a96 b i h).symm)
      exact ⟨hφ,j,(j+1)+1,B4a91 j,hj,(hact _).mpr hk⟩
    · have hk : dist (B4a13 b i j t) (b.c (B4a94 b i (j+1)))=1 := by
        rw [hL,B4a16]
        exact (B4a153 b (B4a94 b i ((j+1)+1))).1 _
          (fun h => B4a187 j (B4a96 b i h))
      exact ⟨hφ,j,j+1,B4a92 j,hj,(hact _).mpr hk⟩
private theorem AS4B.AA_open_sector_parameter (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) (φ : ℝ)
    (hφ : φ ∈ Set.Icc 0 (2*Real.pi)) :
    (φ ∈ sector P j ∧ φ ∉ tieAzimuth P) ↔
      ∃ t ∈ Set.Ioo 0 (B4a75 b i j), B4a13 b i j t=b.c i+exitPoint P φ := by
  constructor
  · rintro ⟨hs,hn⟩
    have ha : φ ∈ activeAzimuth P j := ⟨hφ,by
      change P.rho j φ=P.rho (winner P φ) φ
      rw [hs.2]⟩
    obtain ⟨t,⟨ht,he⟩,_⟩ := (AA_active_parameter b i P hm j φ hφ).mp ha
    have hne : ¬(t=0 ∨ t=B4a75 b i j) := fun h => hn
      ((AA_tie_parameter_endpoints b i P hm j φ t hφ ht he).mpr h)
    exact ⟨t,⟨lt_of_le_of_ne ht.1 (fun h => hne (Or.inl h.symm)),
      lt_of_le_of_ne ht.2 (fun h => hne (Or.inr h))⟩,he⟩
  · rintro ⟨t,ht,he⟩
    have hn : φ ∉ tieAzimuth P := by
      intro hn
      rcases (AA_tie_parameter_endpoints b i P hm j φ t hφ ⟨ht.1.le,ht.2.le⟩ he).mp hn with h | h
      · linarith [ht.1]
      · linarith [ht.2]
    have ha : P.rho j φ=radius P φ := (active_exit_proof P j φ).mpr
      ((matching_inner_sphere hm j _ (exitPoint_mem P φ).1).mpr (by
        rw [← he];exact (B4a18 b i j t).2))
    have hw : winner P φ=j := by
      by_contra hw
      exact hn ⟨hφ,j,winner P φ,fun h => hw h.symm,ha,rfl⟩
    exact ⟨⟨hφ,hw⟩,hn⟩
private theorem AS4B.AA_active_image_actual_arc (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) :
    (fun φ => b.c i+exitPoint P φ) '' activeAzimuth P j =
      B4a13 b i j '' Set.Icc 0 (B4a75 b i j) := by
  rw [HardSphereB5.Lean.Geometry.PathCore.Bridge.active_patch_circle_image P b.c i (B4a94 b i) hm j,
    B4a155]
end AS4Scope20
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore AS4P
open scoped RealInnerProductSpace
section AS4Scope21
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
private theorem AS4B.AA_actual_sector_wrap (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) (q : ℝ → ℝ)
    (hqdiff : Differentiable ℝ q) (hqmono : StrictMono q)
    (hqpoint : ∀ t, polar P.e (P.rho j (q t)) (q t)=B4a13 b i j t-b.c i) :
    sector P j =ᵐ[volume]
      wrapWindow (2*Real.pi) (q 0) (q (B4a75 b i j)) := by
  have hwindow := SolidGeom.CapPolar.capPoint_window_image P j q hqdiff.continuous
    hqmono (B4a75 b i j) (B4a79 b i j)
  have hfin : (tieAzimuth P ∪ ({0,2*Real.pi} : Set ℝ)).Finite :=
    (HardSphereB5.Lean.Geometry.PathCore.Bridge.active_ties_finite b.path b.bulk P i (B4a94 b i) hm).union
      (Set.toFinite _)
  have hnull : volume (tieAzimuth P ∪ ({0,2*Real.pi} : Set ℝ))=0 := hfin.measure_zero volume
  have hav : ∀ᵐ φ : ℝ ∂volume, φ ∉ tieAzimuth P ∪ ({0,2*Real.pi} : Set ℝ) := by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_mem_eq] using hnull
  apply Filter.eventuallyEq_set.mpr
  filter_upwards [hav] with φ hφ
  have hntie : φ ∉ tieAzimuth P := fun h => hφ (Or.inl h)
  have hn0 : φ ≠ 0 := fun h => hφ (Or.inr (by simp [h]))
  have hnT : φ ≠ 2*Real.pi := fun h => hφ (Or.inr (by simp [h]))
  constructor
  · intro hs
    have hdom : φ ∈ Set.Ioo 0 (2*Real.pi) :=
      ⟨lt_of_le_of_ne hs.1.1 (fun h => hn0 h.symm),lt_of_le_of_ne hs.1.2 hnT⟩
    obtain ⟨t,ht,he⟩ := (AA_open_sector_parameter b i P hm j φ hs.1).mp ⟨hs,hntie⟩
    have ha : P.rho j φ=radius P φ := by
      change P.rho j φ=P.rho (winner P φ) φ
      rw [hs.2]
    have hc : polar P.e (P.rho j φ) φ=B4a13 b i j t-b.c i := by
      rw [ha]
      change exitPoint P φ=B4a13 b i j t-b.c i
      rw [he]
      abel
    rw [hwindow]
    refine ⟨hdom,t,ht,?_⟩
    change polar P.e (P.rho j (q t)) (q t)=polar P.e (P.rho j φ) φ
    rw [hqpoint,hc]
  · intro hw
    rw [hwindow] at hw
    obtain ⟨hdom,t,ht,he⟩ := hw
    change polar P.e (P.rho j (q t)) (q t)=polar P.e (P.rho j φ) φ at he
    rw [hqpoint] at he
    have hc : b.c i+polar P.e (P.rho j φ) φ=B4a13 b i j t := by
      rw [← he]
      abel
    have hp : polar P.e (P.rho j φ) φ ∈ caps P :=
      (matching_patch_iff hm _).mpr (hc.symm ▸ B4a159 b i j t ⟨ht.1.le,ht.2.le⟩)
    have hr : P.rho j φ=radius P φ := le_antisymm
      ((ray_membership P (P.rho j φ) φ
        ⟨(P.rho_range j φ).1.le,(P.rho_range j φ).2.le⟩).mp hp)
      (winner_min P φ j)
    have hext : B4a13 b i j t=b.c i+exitPoint P φ := by
      change B4a13 b i j t=b.c i+polar P.e (radius P φ) φ
      rw [← hr]
      exact hc.symm
    exact ((AA_open_sector_parameter b i P hm j φ ⟨hdom.1.le,hdom.2.le⟩).mpr
      ⟨t,ht,hext⟩).1
end AS4Scope21
private lemma SolidGeom.CapPolar.Window_polar_period (e : Fin 3 → E3) (r φ : ℝ) (k : ℤ) :
    polar e r (φ+(k:ℝ)*(2*Real.pi))=polar e r φ := by
  simp only [polar,Real.cos_add_int_mul_two_pi,Real.sin_add_int_mul_two_pi]
private lemma SolidGeom.CapPolar.Window_rho_period (P : Profile) (j : Fin 3) (φ : ℝ) (k : ℤ) :
    P.rho j (φ+(k:ℝ)*(2*Real.pi))=P.rho j φ := by
  let a := inner ℝ (P.normal j) (P.e 2)
  let b := Real.cos φ*inner ℝ (P.normal j) (P.e 0)+Real.sin φ*inner ℝ (P.normal j) (P.e 1)
  have hexp : ∀ t : ℝ, inner ℝ (P.normal j) (polar P.e t φ)=a*Real.cos t+b*Real.sin t := by
    intro t
    unfold polar
    simp only [inner_add_right,real_inner_smul_right]
    dsimp [a,b]
    ring
  have hr : a*Real.cos (P.rho j φ)+b*Real.sin (P.rho j φ)=P.height j := by
    rw [← hexp]
    exact P.ray_boundary j φ
  apply (ray_equal_root a b (P.height j) (P.rho j φ)
    (P.rho j (φ+(k:ℝ)*(2*Real.pi))) (P.height_pos j) (P.pole_inside j)
    (P.rho_range j φ) (P.rho_range j _) hr).mp
  rw [← hexp,← Window_polar_period P.e _ φ k]
  exact P.ray_boundary j _
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore AS4P
open scoped RealInnerProductSpace
section AS4Scope22
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
private lemma AS4B.AGC_cyclic_three (j : Fin 3) : (((j+1)+1)+1)=j := by
  fin_cases j <;> rfl
private theorem AS4B.AGC_actual_corner_positive (b : B4a0) (i : Fin 4) (j : Fin 3) :
    0 < inner ℝ (B4a42 b i j-b.c i)
      (SphereGeom.cross (b.c (B4a94 b i j)-b.c i)
        (b.c (B4a94 b i (j+1))-b.c i)) := by
  let u := B4a42 b i j-b.c i
  let v := b.c (B4a94 b i j)-b.c i
  let w := b.c (B4a94 b i (j+1))-b.c i
  have H := B4a158 b i (j+1)
  rw [AGC_cyclic_three,← B4a151] at H
  have he : inner ℝ v (SphereGeom.cross w u)=inner ℝ u (SphereGeom.cross v w) := by
    simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,Fin.sum_univ_succ]
    ring
  have hscaled : 0 < (dist (b.c i) (b.c (B4a94 b i (j+1))))⁻¹*
      inner ℝ u (SphereGeom.cross v w) := by
    simpa only [B4a10,B4a164,real_inner_smul_right,he,v,w,u] using H
  change 0 < inner ℝ u (SphereGeom.cross v w)
  by_contra hnot
  have hn : inner ℝ u (SphereGeom.cross v w) ≤ 0 := le_of_not_gt hnot
  have hi := inv_nonneg.mpr (B4a38 b i (j+1)).1.le
  have hh := mul_nonpos_of_nonneg_of_nonpos hi hn
  linarith
private theorem AS4B.AGC_actual_center_corner_gamma (b : B4a0) (i : Fin 4) (j : Fin 3) :
    capCorner (B4a42 b i j-b.c i)
      (b.c (B4a94 b i j)-b.c i) (b.c (B4a94 b i (j+1))-b.c i)=
        gammaA b.c i (B4a94 b i j) (B4a94 b i (j+1)) := by
  let u := B4a42 b i j-b.c i
  let v := b.c (B4a94 b i j)-b.c i
  let w := b.c (B4a94 b i (j+1))-b.c i
  have hj := B4a45 b i j
  have hk := B4a146 b i (j+1)
  rw [← B4a151] at hk
  have hu : ‖u‖=1 := by
    simpa only [u,Metric.mem_sphere,dist_eq_norm] using hj.1
  have hv : ‖u-v‖=1 := by
    have he : u-v=B4a42 b i j-b.c (B4a94 b i j) := by dsimp [u,v];abel
    rw [he]
    simpa only [Metric.mem_sphere,dist_eq_norm] using hj.2
  have hw : ‖u-w‖=1 := by
    have he : u-w=B4a42 b i j-b.c (B4a94 b i (j+1)) := by dsimp [u,w];abel
    rw [he]
    simpa only [Metric.mem_sphere,dist_eq_norm] using hk.2
  exact SolidGeom.CapPolar.capCorner_gamma b.c i (B4a94 b i j) (B4a94 b i (j+1))
    u hu hv hw (AGC_actual_corner_positive b i j)
private theorem AS4B.AGC_actual_axes_corner_gamma (b : B4a0) (i : Fin 4) (j : Fin 3) :
    capCorner (B4a42 b i j-b.c i) (B4a10 b i j) (B4a10 b i (j+1))=
      gammaA b.c i (B4a94 b i j) (B4a94 b i (j+1)) := by
  unfold B4a10
  rw [SolidGeom.CapPolar.capCorner_pos_smul _ _ _ _ _
    (inv_pos.mpr (B4a38 b i j).1)
    (inv_pos.mpr (B4a38 b i (j+1)).1)]
  exact AGC_actual_center_corner_gamma b i j
private theorem AS4B.AGC_actual_profile_corner_gamma (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) :
    capCorner (B4a42 b i j-b.c i) (P.normal j) (P.normal (j+1))=
      gammaA b.c i (B4a94 b i j) (B4a94 b i (j+1)) := by
  rw [hm.normal_eq j,hm.normal_eq (j+1)]
  exact AGC_actual_axes_corner_gamma b i j
private theorem AS4B.AGC_sum_actual_profile_corners (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) :
    (∑ j : Fin 3, capCorner (B4a42 b i j-b.c i) (P.normal j) (P.normal (j+1)))=
      ∑ j : Fin 3, gammaA b.c i (B4a94 b i j) (B4a94 b i (j+1)) := by
  apply Finset.sum_congr rfl
  intro j hj
  exact AGC_actual_profile_corner_gamma b i P hm j
end AS4Scope22
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope23
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
open SphereGeom SolidGeom.CapPolar
private theorem AS4B.B4D_orientedProfile_exists (b : B4a0) (i : Fin 4) :
    ∃ P : Profile, BulkMatching P b.c i (B4a94 b i) ∧
      SphereGeom.cross (P.e 2) (P.e 0)=P.e 1 := by
  let n : Fin 3 → Pt := B4a10 b i
  let h : Fin 3 → ℝ := B4a63 b i
  have hn : ∀ j, ‖n j‖=1 := by
    intro j
    have H := (B4a50 b i j).aa
    rw [real_inner_self_eq_norm_sq] at H
    exact (sq_eq_one_iff).mp H |>.resolve_right (by nlinarith [norm_nonneg (n j)])
  have hh : ∀ j, 0 < h j := by
    intro j
    exact div_pos (B4a38 b i j).1 (by norm_num)
  have hi : ∀ j, h j < inner ℝ (n j) (B4a65 b i) := by
    intro j
    have hd := (B4a38 b i j).1
    have H := B4a66 b i j
    have he : ‖b.c (B4a94 b i j)-b.c i‖=dist (b.c i) (b.c (B4a94 b i j)) := by
      rw [dist_eq_norm,norm_sub_rev]
    rw [he] at H
    dsimp [n,h,B4a10,B4a63]
    rw [real_inner_smul_left,inv_mul_eq_div,lt_div_iff₀ hd]
    nlinarith [H]
  obtain ⟨P,hpole,hor,hnorm,hheight⟩ := profile_of_unit_oriented
    (B4a65 b i) (B4a67 b i) n hn h hh hi
  refine ⟨P,⟨B4a97 b i,B4a96 b i,?_,?_⟩,hor⟩
  · intro j
    rw [hnorm]
    rfl
  · intro j
    rw [hheight]
    rfl
private theorem AS4B.B4D_actualCapFrame (b : B4a0) (i : Fin 4) (j : Fin 3) :
    Orthonormal ℝ (fun k : Fin 3 => ![B4a10 b i j,B4a39 b i j,B4a40 b i j] k) := by
  have F := B4a50 b i j
  have h10 : inner ℝ (B4a39 b i j) (B4a10 b i j)=0 := (real_inner_comm _ _).trans F.ae1
  have h20 : inner ℝ (B4a40 b i j) (B4a10 b i j)=0 := (real_inner_comm _ _).trans F.ae2
  have h21 : inner ℝ (B4a40 b i j) (B4a39 b i j)=0 := (real_inner_comm _ _).trans F.e12
  apply orthonormal_iff_ite.mpr
  intro k l
  fin_cases k <;> fin_cases l
  all_goals first | exact F.aa | exact F.ae1 | exact F.ae2 | exact h10 | exact F.e11 | exact F.e12 | exact h20 | exact h21 | exact F.e22
private theorem AS4B.B4D_actualCap_chart (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) (C : AlignedCap P j) :
    ∃ q : ℝ → ℝ, Differentiable ℝ q ∧ StrictMono q ∧
      (∀ t, q (t+2*Real.pi)=q t+2*Real.pi) ∧
      (∀ t, polar P.e (P.rho j (q t)) (q t)=B4a13 b i j t-b.c i) ∧
      (∀ t, capExitPoint (P.e 2) C.a C.b C.A (P.height j) (q t-C.δ)=
        B4a13 b i j t-b.c i) := by
  have hnormal : P.normal j=B4a10 b i j := hm.normal_eq j
  have hheight : P.height j=B4a63 b i j := hm.height_eq j
  have haxis : B4a10 b i j=capAxis (P.e 2) C.a C.A := hnormal.symm.trans C.normal_eq
  have hG : SphereGeom.cross (B4a10 b i j) (B4a39 b i j)=B4a40 b i j := rfl
  obtain ⟨r,hrd,hrm,hrp,hrpoint⟩ := cap_circle_polar_chart_ordered
    (P.e 2) C.a C.b (B4a10 b i j) (B4a39 b i j) (B4a40 b i j) C.A (P.height j)
    C.bounds.1 C.bounds.2.1 C.bounds.2.2 C.frame C.oriented haxis
    (B4D_actualCapFrame b i j) hG
  have hpoint : ∀ t, capExitPoint (P.e 2) C.a C.b C.A (P.height j) (r t)=
      B4a13 b i j t-b.c i := by
    intro t
    rw [hrpoint,hheight]
    change Gnomonic.capArc (B4a10 b i j) (B4a39 b i j) (B4a40 b i j)
      (B4a63 b i j) t=B4a13 b i j t-b.c i
    exact (B4a20 b i j t).symm
  let q : ℝ → ℝ := fun t => r t+C.δ
  refine ⟨q,hrd.add_const C.δ,?_,?_,?_,?_⟩
  · intro x y hxy
    simpa only [q,add_comm] using add_lt_add_right (hrm hxy) C.δ
  · intro t
    dsimp only [q]
    rw [hrp]
    ring
  · intro t
    rw [C.point_eq]
    dsimp only [q]
    rw [add_sub_cancel_right]
    exact hpoint t
  · intro t
    dsimp only [q]
    rw [add_sub_cancel_right]
    exact hpoint t
private theorem AS4B.B4D_actualCapData_exists (b : B4a0) (i : Fin 4) :
    ∃ P : Profile, BulkMatching P b.c i (B4a94 b i) ∧
      SphereGeom.cross (P.e 2) (P.e 0)=P.e 1 ∧
      ∀ j : Fin 3, ∃ C : AlignedCap P j, ∃ q : ℝ → ℝ,
        Differentiable ℝ q ∧ StrictMono q ∧
        (∀ t, q (t+2*Real.pi)=q t+2*Real.pi) ∧
        (∀ t, polar P.e (P.rho j (q t)) (q t)=B4a13 b i j t-b.c i) ∧
        (∀ t, capExitPoint (P.e 2) C.a C.b C.A (P.height j) (q t-C.δ)=
          B4a13 b i j t-b.c i) := by
  obtain ⟨P,hm,hor⟩ := B4D_orientedProfile_exists b i
  refine ⟨P,hm,hor,?_⟩
  intro j
  obtain ⟨C⟩ := alignedCap_exists P hor j
  exact ⟨C,B4D_actualCap_chart b i P hm j C⟩
end AS4Scope23
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore AS4P
open scoped RealInnerProductSpace
section AS4Scope24
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
private lemma AS4B.AS4_rho_period (P : Profile) (j : Fin 3) : Function.Periodic (P.rho j) (2*Real.pi) := by
  intro φ
  simpa using Window_rho_period P j φ 1
private lemma AS4B.AS4_sector_interval (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) (q : ℝ → ℝ)
    (hd : Differentiable ℝ q) (hmq : StrictMono q)
    (hperiod : ∀ t, q (t+2*Real.pi)=q t+2*Real.pi)
    (hpoint : ∀ t, polar P.e (P.rho j (q t)) (q t)=B4a13 b i j t-b.c i)
    (f : ℝ → ℝ) (hf : Continuous f) (hfp : Function.Periodic f (2*Real.pi)) :
    (∫ φ in sector P j, f φ)=∫ φ in (q 0)..(q (B4a75 b i j)), f φ := by
  rw [setIntegral_congr_set (AA_actual_sector_wrap b i P hm j q hd hmq hpoint)]
  apply wrapWindow_integral_any f hf (2*Real.pi) (q 0) (q (B4a75 b i j))
    (by positivity) (hmq (B4a79 b i j))
  · have hh := hmq (B4a77 b i j)
    have he : q (2*Real.pi)=q 0+2*Real.pi := by
      simpa only [zero_add] using hperiod 0
    rwa [he] at hh
  · exact hfp
private lemma AS4B.AS4_cap_angular_increment (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (j : Fin 3) (C : AlignedCap P j)
    (q : ℝ → ℝ) (hd : Differentiable ℝ q)
    (hlocal : ∀ t, capExitPoint (P.e 2) C.a C.b C.A (P.height j) (q t-C.δ)=
      B4a13 b i j t-b.c i) :
    momentAzimuth C.A (P.height j) (q (B4a75 b i j)-C.δ)-
      momentAzimuth C.A (P.height j) (q 0-C.δ)=B4a75 b i j := by
  apply cap_arc_azimuth_increment (P.e 2) C.a C.b (B4a10 b i j) (B4a39 b i j)
    (B4a40 b i j) C.A (P.height j) (B4a75 b i j) (fun t => q t-C.δ) Set.univ
    C.bounds.1 C.bounds.2.1 C.bounds.2.2 (B4a79 b i j) C.frame C.oriented
    ((hm.normal_eq j).symm.trans C.normal_eq) (B4D_actualCapFrame b i j) rfl isOpen_univ
    (Set.subset_univ _) (hd.sub_const C.δ).differentiableOn
  intro t ht
  change capExitPoint (P.e 2) C.a C.b C.A (P.height j) (q t-C.δ)=
    P.height j • B4a10 b i j+Real.sqrt (1-(P.height j)^2) •
      (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j)
  have hr : Real.sqrt (1-(B4a63 b i j)^2)=B4a116 b i j := by
    unfold B4a63 B4a116 HardSphereB5.Lean.Geometry.PathCore.q
    congr 1
    ring
  rw [hlocal,hm.height_eq]
  change B4a13 b i j t-b.c i=B4a63 b i j • B4a10 b i j+
    Real.sqrt (1-(B4a63 b i j)^2) • (Real.cos t • B4a39 b i j+Real.sin t • B4a40 b i j)
  rw [hr]
  exact (B4a118 b i j t).symm
private theorem AS4B.AS4_area_application (b : B4a0) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (B4a94 b i)) (C : ∀ j : Fin 3, AlignedCap P j)
    (q : Fin 3 → ℝ → ℝ) (hd : ∀ j, Differentiable ℝ (q j))
    (hmq : ∀ j, StrictMono (q j))
    (hperiod : ∀ j t, q j (t+2*Real.pi)=q j t+2*Real.pi)
    (hpoint : ∀ j t, polar P.e (P.rho j (q j t)) (q j t)=B4a13 b i j t-b.c i)
    (hlocal : ∀ j t, capExitPoint (P.e 2) (C j).a (C j).b (C j).A (P.height j) (q j t-(C j).δ)=
      B4a13 b i j t-b.c i) :
    pArea b.c i Finset.univ=2*Real.pi-
      (∑ j : Fin 3, gammaA b.c i (B4a94 b i j) (B4a94 b i (j+1)))-
      (∑ j : Fin 3, B4a63 b i j*B4a75 b i j) := by
  let α : Fin 3 → ℝ := fun j => q j 0-(C j).δ
  let om : Fin 3 → ℝ := fun j => q j (B4a75 b i j)-(C j).δ
  have hwidth (j : Fin 3) : (∫ φ in sector P j, (1:ℝ))=om j-α j := by
    rw [AS4_sector_interval b i P hm j (q j) (hd j) (hmq j) (hperiod j) (hpoint j)
      (fun _ => (1:ℝ)) continuous_const (by intro t;rfl)]
    simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one]
    dsimp [α,om]
    ring
  have hsumwidth : (∑ j : Fin 3, (om j-α j))=2*Real.pi := by
    rw [← sector_width_sum P]
    exact Finset.sum_congr rfl (fun j _ => (hwidth j).symm)
  have harea (j : Fin 3) :
      (∫ φ in sector P j, (1-Real.cos (P.rho j φ)))=
        ∫ ψ in (α j)..(om j), areaDensity ((C j).A) (P.height j) ψ := by
    rw [AS4_sector_interval b i P hm j (q j) (hd j) (hmq j) (hperiod j) (hpoint j)
      (fun φ => 1-Real.cos (P.rho j φ))
      (continuous_const.sub (Real.continuous_cos.comp (P.rho_continuous j)))
      (by intro φ;dsimp only;rw [(AS4_rho_period P j) φ])]
    rw [aligned_area_integral P j (C j),sector_area_primitive ((C j).A) (P.height j)
      (α j) (om j) (C j).bounds.1 (C j).bounds.2.1 (C j).bounds.2.2]
  have hp : inner ℝ (P.e 2) (P.e 2)=1 := by
    simpa using (orthonormal_iff_ite.mp P.frame) 2 2
  have ha (j : Fin 3) : inner ℝ (C j).a (C j).a=1 := by
    simpa using (orthonormal_iff_ite.mp (C j).frame) 1 1
  have hpa (j : Fin 3) : inner ℝ (P.e 2) (C j).a=0 := by
    simpa using (orthonormal_iff_ite.mp (C j).frame) 0 1
  have hglue (j : Fin 3) :
      capExitPoint (P.e 2) (C j).a (C j).b (C j).A (P.height j) (om j)=
        capExitPoint (P.e 2) (C (j+1)).a (C (j+1)).b (C (j+1)).A
          (P.height (j+1)) (α (j+1)) := by
    dsimp [α,om]
    rw [hlocal,hlocal,B4a16,B4a21,B4a151]
  have HB := area_sectors_boundary_sum 2 (P.e 2) (fun j => (C j).a) (fun j => (C j).b)
    (fun j => (C j).A) P.height α om (fun j => (C j).bounds.1)
    (fun j => (C j).bounds.2.1) (fun j => (C j).bounds.2.2)
    hp ha hpa (fun j => (C j).oriented) hglue
  have hinc (j : Fin 3) :
      momentAzimuth (C j).A (P.height j) (om j)-momentAzimuth (C j).A (P.height j) (α j)=
        B4a75 b i j := AS4_cap_angular_increment b i P hm j (C j) (q j) (hd j) (hlocal j)
  have hcorner (j : Fin 3) :
      capCorner (capExitPoint (P.e 2) (C j).a (C j).b (C j).A (P.height j) (om j))
        (capAxis (P.e 2) (C j).a (C j).A)
        (capAxis (P.e 2) (C (j+1)).a (C (j+1)).A)=
          gammaA b.c i (B4a94 b i j) (B4a94 b i (j+1)) := by
    dsimp [om]
    rw [hlocal,B4a16,← (C j).normal_eq,← (C (j+1)).normal_eq]
    exact AGC_actual_profile_corner_gamma b i P hm j
  simp_rw [hinc,hcorner] at HB
  rw [hsumwidth] at HB
  have HP := (HardSphereB5.Lean.Geometry.PathCore.Bridge.profile_patch_measure hm).1
  rw [area_eq_polar_sectors P] at HP
  simp_rw [harea] at HP
  rw [HP,HB]
  simp only [hm.height_eq,B4a63]
  ring
end AS4Scope24
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AS4Scope25
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
open HardSphereB5.Lean (Pt)
private theorem AS4B.ALJ_actual_pair_arc (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a13 b i j '' Set.Icc 0 (B4a75 b i j) =
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1 ∩ Kset b.c := by
  rw [B4a155]
  ext p
  simp only [patch,Set.mem_inter_iff]
  exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,
    fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
private theorem AS4B.ALJ_pair_arcMeasure (b : B4a0) (i : Fin 4) (j : Fin 3) :
    SphereGeom.arcMeasure
      (Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1 ∩ Kset b.c) =
      ENNReal.ofReal (B4a116 b i j * B4a75 b i j) := by
  rw [← ALJ_actual_pair_arc]
  change SphereGeom.arcMeasure
    (SphereGeom.circlePt (B4a89 b i j) (B4a39 b i j) (B4a40 b i j)
      (B4a116 b i j) '' Set.Icc 0 (B4a75 b i j)) = _
  have h := SphereGeom.arcMeasure_circle_arc (B4a89 b i j)
    ![B4a39 b i j,B4a40 b i j] (B4a52 b i j)
    (B4a116 b i j) (B4a117 b i j) 0 (B4a75 b i j)
    (B4a79 b i j).le (by simpa only [sub_zero] using (B4a77 b i j).le)
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,sub_zero] using h
private theorem AS4B.ALJ_pair_arcMeasure_toReal (b : B4a0) (i : Fin 4) (j : Fin 3) :
    (SphereGeom.arcMeasure
      (Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (B4a94 b i j)) 1 ∩ Kset b.c)).toReal =
      B4a116 b i j * B4a75 b i j := by
  rw [ALJ_pair_arcMeasure,ENNReal.toReal_ofReal
    (mul_nonneg (B4a117 b i j).le (B4a79 b i j).le)]
private theorem AS4B.ALJ_len_eq_ell (b : B4a0) (i : Fin 4) (j : Fin 3) :
    B4a75 b i j = ell b.c i (B4a94 b i j) := by
  unfold ell
  rw [ALJ_pair_arcMeasure_toReal]
  change B4a75 b i j = (B4a116 b i j*B4a75 b i j)/B4a116 b i j
  exact (mul_div_cancel_left₀ (B4a75 b i j) (ne_of_gt (B4a117 b i j))).symm
private theorem AS4B.ALJ_ell_eq_len (b : B4a0) (i : Fin 4) (j : Fin 3) :
    ell b.c i (B4a94 b i j) = B4a75 b i j := (ALJ_len_eq_ell b i j).symm
private theorem AS4B.ALJ_boundary_length_eq_ell (b : B4a0) (i : Fin 4) (j : Fin 3) :
    (B4a188 b i).len j = ell b.c i (B4a94 b i j) := by
  rw [B4a191]
  exact ALJ_len_eq_ell b i j
end AS4Scope25
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore AS4P
open scoped RealInnerProductSpace
section AS4Scope26
open HardSphereB5.Lean.Geometry.PathCore AS4P AS4B
private lemma AS4B.AS4_gamma_pair_symm (c : Fin 4 → Pt) (i j k : Fin 4) : gammaA c i j k=gammaA c i k j := by
  unfold gammaA
  have hq : q c k j=q c j k := by unfold q;rw [dist_comm]
  have hQ : Qf c i j k=Qf c i k j := by
    unfold Qf QT DeltaT
    rw [hq]
    ring
  rw [hQ,hq]
  congr 1
  ring
private lemma AS4B.AS4_gamma_reindex (b : B4a0) (i : Fin 4) :
    (∑ j : Fin 3, gammaA b.c i (B4a94 b i j) (B4a94 b i (j+1)))=
      (∑ l : Fin 4, if l≠i then gammaA b.c i (oth1 i l) (oth2 i l) else 0) := by
  by_cases hd : det3 (b.c (B4a98 i 0)-b.c i) (b.c (B4a98 i 1)-b.c i)
    (b.c (B4a98 i 2)-b.c i)<0
  all_goals simp only [B4a94,hd,if_true,if_false]
  all_goals fin_cases i <;> simp [B4a98,B4a48,Fin.sum_univ_succ,oth1,oth2]
  all_goals simp only [AS4_gamma_pair_symm]
  all_goals abel
private lemma AS4B.AS4_height_length_reindex (b : B4a0) (i : Fin 4) :
    (∑ j : Fin 3, B4a63 b i j*B4a75 b i j)=
      (1/2)*(∑ j : Fin 4, if j≠i then dist (b.c i) (b.c j)*ell b.c i j else 0) := by
  simp_rw [B4a63,ALJ_len_eq_ell]
  have he : (∑ j : Fin 3, dist (b.c i) (b.c (B4a94 b i j))/2*ell b.c i (B4a94 b i j))=
      (1/2)*(∑ j : Fin 3, dist (b.c i) (b.c (B4a94 b i j))*ell b.c i (B4a94 b i j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  congr 1
  by_cases hd : det3 (b.c (B4a98 i 0)-b.c i) (b.c (B4a98 i 1)-b.c i)
    (b.c (B4a98 i 2)-b.c i)<0
  all_goals simp only [B4a94,hd,if_true,if_false]
  all_goals fin_cases i <;> simp [B4a98,B4a48,Fin.sum_univ_succ] <;> abel
private theorem AS4B.AS4_actual_patch_area_raw (b : B4a0) (i : Fin 4) :
    pArea b.c i Finset.univ=2*Real.pi-
      (∑ l : Fin 4, if l≠i then gammaA b.c i (oth1 i l) (oth2 i l) else 0)-
      (1/2)*(∑ j : Fin 4, if j≠i then dist (b.c i) (b.c j)*ell b.c i j else 0) := by
  classical
  obtain ⟨P,hm,hor,hdata⟩ := B4D_actualCapData_exists b i
  choose C q hd hmq hperiod hpoint hlocal using hdata
  have H := AS4_area_application b i P hm C q hd hmq hperiod hpoint hlocal
  rw [AS4_gamma_reindex,AS4_height_length_reindex] at H
  exact H
end AS4Scope26
open AS4B
theorem proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_area_identity {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : 0<P4poly X Y s) (i : Fin 4) :
    pArea c i Finset.univ=2*Real.pi-
      (∑ l : Fin 4, if l≠i then gammaA c i (oth1 i l) (oth2 i l) else 0)-
      (1/2)*(∑ j : Fin 4, if j≠i then dist (c i) (c j)*ell c i j else 0) := by
  let b : B4a0 := ⟨c,X,Y,s,hc,hP⟩
  exact AS4_actual_patch_area_raw b i
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_area_identity
