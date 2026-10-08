import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_sector_moment_primitive
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_aligned_moment_integral
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_cyclic_sector_moment_boundary_sum
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_cap_arc_azimuth_increment
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_wrapWindow_integral_any
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_moment_eq_polar_sectors
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Bridge_profile_patch_measure
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_patch_circle_image
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_ties_finite
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_capPoint_window_image
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
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
local notation "cross" => HardSphereB5.Lean.Geometry.PathCore.cross
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Real
section AreaScope1
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000
private def M4.TripleGeometry.sq (x : Pt) : ℝ := ⟪x, x⟫
open M4.TripleGeometry
private def M4.TripleGeometry.faceDelta (v w : Pt) : ℝ := DeltaT (sq v) (sq w) (sq (v - w))
private def M4.TripleGeometry.faceQ (v w : Pt) : ℝ := QT (sq v) (sq w) (sq (v - w))
private def M4.TripleGeometry.center (v w : Pt) : Pt :=
  (sq w * (sq v - sq w + sq (v - w)) / faceDelta v w) • v +
  (sq v * (sq w - sq v + sq (v - w)) / faceDelta v w) • w
private def M4.TripleGeometry.height (v w : Pt) : ℝ := Real.sqrt (faceQ v w / faceDelta v w)
private def M4.TripleGeometry.orientedNormal (v w z : Pt) : Pt :=
  if 0 < ⟪z, cross v w⟫ then ‖cross v w‖⁻¹ • cross v w
  else -(‖cross v w‖⁻¹ • cross v w)
private def M4.TripleGeometry.triple (v w : Pt) : Set Pt := {x | ‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1}
private lemma M4.TripleGeometry.sq_eq_norm_sq (x : Pt) : sq x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
private lemma M4.TripleGeometry.sq_nonneg (x : Pt) : 0 ≤ sq x := by rw [sq_eq_norm_sq]; positivity
private lemma M4.TripleGeometry.sq_sub (x y : Pt) : sq (x - y) = sq x + sq y - 2 * ⟪x, y⟫ := by
  simp only [sq, inner_sub_left, inner_sub_right, real_inner_comm y x]
  ring
private lemma M4.TripleGeometry.sq_eq_one_iff (x : Pt) : sq x = 1 ↔ ‖x‖ = 1 := by
  rw [sq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg x]
  · intro h; rw [h]; norm_num
private lemma M4.TripleGeometry.inner_coords (x y : Pt) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]
private lemma M4.TripleGeometry.cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1,
      v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := by
  simp [HardSphereB5.Lean.Geometry.PathCore.cross, SphereGeom.cross, cross_apply]
private lemma M4.TripleGeometry.cross_v (v w : Pt) : ⟪v, cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma M4.TripleGeometry.cross_w (v w : Pt) : ⟪w, cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma M4.TripleGeometry.cross_sq (v w : Pt) :
    sq (cross v w) = sq v * sq w - ⟪v, w⟫ ^ 2 := by
  simp only [sq, inner_coords, cross_coords]
  simp
  ring
private lemma M4.TripleGeometry.gram_resolution (v w x : Pt) :
    (sq v * sq w - ⟪v, w⟫ ^ 2) • x =
      (sq w * ⟪v, x⟫ - ⟪v, w⟫ * ⟪w, x⟫) • v +
      (sq v * ⟪w, x⟫ - ⟪v, w⟫ * ⟪v, x⟫) • w +
      ⟪cross v w, x⟫ • cross v w := by
  simp only [sq, inner_coords]
  ext i
  fin_cases i <;> simp [cross_coords] <;> ring
private lemma M4.TripleGeometry.delta_gram (v w : Pt) :
    faceDelta v w = 4 * (sq v * sq w - ⟪v, w⟫ ^ 2) := by
  simp only [faceDelta, DeltaT, sq_sub]
  ring
private lemma M4.TripleGeometry.q_delta (v w : Pt) :
    faceQ v w = faceDelta v w - sq v * sq w * sq (v - w) := rfl
private lemma M4.TripleGeometry.center_inner_v (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, v⟫ = sq v / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq, real_inner_comm w v]
  ring
private lemma M4.TripleGeometry.center_inner_w (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, w⟫ = sq w / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq]
  ring
private lemma M4.TripleGeometry.center_sq (v w : Pt) (hD : faceDelta v w ≠ 0) :
    sq (center v w) = sq v * sq w * sq (v - w) / faceDelta v w := by
  change ⟪center v w, center v w⟫ = _
  nth_rw 2 [center]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    center_inner_v v w hD, center_inner_w v w hD]
  ring
private lemma M4.TripleGeometry.cross_norm_pos (v w : Pt) (hD : 0 < faceDelta v w) : 0 < ‖cross v w‖ := by
  have he := delta_gram v w
  have hs := cross_sq v w
  rw [sq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cross v w)]
private lemma M4.TripleGeometry.unit_cross_norm (v w : Pt) (hD : 0 < faceDelta v w) :
    ‖‖cross v w‖⁻¹ • cross v w‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cross_norm_pos v w hD))]
  exact inv_mul_cancel₀ (ne_of_gt (cross_norm_pos v w hD))
private lemma M4.TripleGeometry.normal_norm (v w z : Pt) (hD : 0 < faceDelta v w) :
    ‖orientedNormal v w z‖ = 1 := by
  unfold orientedNormal
  split_ifs <;> simp only [norm_neg, unit_cross_norm v w hD]
private lemma M4.TripleGeometry.normal_sq (v w z : Pt) (hD : 0 < faceDelta v w) :
    sq (orientedNormal v w z) = 1 := by
  rw [sq_eq_norm_sq, normal_norm v w z hD]; norm_num
private lemma M4.TripleGeometry.normal_v (v w z : Pt) : ⟪v, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_v]
private lemma M4.TripleGeometry.normal_w (v w z : Pt) : ⟪w, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_w]
private lemma M4.TripleGeometry.normal_oriented (v w z : Pt) (hD : 0 < faceDelta v w)
    (hG : ⟪z, cross v w⟫ ≠ 0) : 0 < ⟪z, orientedNormal v w z⟫ := by
  have hi := inv_pos.mpr (cross_norm_pos v w hD)
  unfold orientedNormal
  split_ifs with hz
  · rw [real_inner_smul_right]; exact mul_pos hi hz
  · rw [inner_neg_right, real_inner_smul_right]
    have hz' : ⟪z, cross v w⟫ < 0 := lt_of_le_of_ne (le_of_not_gt hz) hG
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hi hz')
private lemma M4.TripleGeometry.center_normal (v w z : Pt) : ⟪center v w, orientedNormal v w z⟫ = 0 := by
  simp only [center, inner_add_left, real_inner_smul_left, normal_v, normal_w,
    mul_zero, add_zero]
private lemma M4.TripleGeometry.perp_as_normal (v w z d : Pt) (hD : 0 < faceDelta v w)
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
private lemma M4.TripleGeometry.height_pos (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    0 < height v w := Real.sqrt_pos.mpr (div_pos hQ hD)
private lemma M4.TripleGeometry.center_height (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    sq (center v w) + height v w ^ 2 = 1 := by
  rw [center_sq v w (ne_of_gt hD)]
  unfold height
  rw [Real.sq_sqrt (le_of_lt (div_pos hQ hD)), q_delta]
  field_simp [ne_of_gt hD]
  ring
private lemma M4.TripleGeometry.mem_triple_iff (v w x : Pt) :
    x ∈ triple v w ↔ sq x = 1 ∧ ⟪x, v⟫ = sq v / 2 ∧ ⟪x, w⟫ = sq w / 2 := by
  change (‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1) ↔ _
  simp only [← sq_eq_one_iff, sq_sub]
  constructor
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
private lemma M4.TripleGeometry.center_line_sq (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w) :
    sq (center v w + r • orientedNormal v w z) = sq (center v w) + r ^ 2 := by
  have ho := center_normal v w z
  have hn : ⟪orientedNormal v w z, orientedNormal v w z⟫ = 1 := normal_sq v w z hD
  have ho' : ⟪orientedNormal v w z, center v w⟫ = 0 := (real_inner_comm (center v w) _).trans ho
  simp only [sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ho, ho', hn]
  ring
private lemma M4.TripleGeometry.line_mem_triple (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
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
private theorem M4.TripleGeometry.triple_exact (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
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
private lemma M4.TripleGeometry.cross_gram_identity (v w z : Pt) :
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
private lemma M4.TripleGeometry.triple_points_ne (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
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
private theorem M4.TripleGeometry.fourth_sq_formula (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hr : r ^ 2 = height v w ^ 2) :
    ‖center v w + r • orientedNormal v w z - z‖ ^ 2 - 1 =
      sq z - 2 * ⟪z, center v w⟫ - 2 * r * ⟪z, orientedNormal v w z⟫ := by
  rw [← sq_eq_norm_sq, sq_sub, center_line_sq v w z r hD,
    inner_add_left, real_inner_smul_left, real_inner_comm z (center v w),
    real_inner_comm z (orientedNormal v w z), hr]
  linarith [center_height v w hD hQ]
end
end AreaScope1
section AreaScope2
open M4
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
private lemma M4.q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]
private lemma M4.q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]
private lemma M4.inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith
private def M4.Dpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![DeltaT X 1 s, DeltaT 1 Y s, DeltaT 1 Y 1, DeltaT 1 1 X]
private def M4.gramPoly (a b cc d e f : ℝ) : ℝ :=
  4*a*b*d + (a+b-cc)*(a+d-e)*(b+d-f)
    - a*(b+d-f)^2 - b*(a+d-e)^2 - d*(a+b-cc)^2
private def M4.faceAPoly (a b cc d e f : ℝ) : ℝ :=
  DeltaT a b cc * d - b*(a-b+cc)*(a+d-e) - a*(b-a+cc)*(b+d-f)
private lemma M4.face_polys (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
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
private lemma M4.cayley_menger_face_identity (X Y s : ℝ) (l : Fin 4) :
    Apoly X Y s l ^ 2 - 4 * Hpoly X Y s * Qpoly X Y s l =
      -Dpoly X Y s l * P4poly X Y s := by
  fin_cases l <;> simp [Apoly, Hpoly, Qpoly, Dpoly, DeltaT, P4poly] <;> ring
private lemma M4.cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z)^2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z)^2 -
      inner ℝ w w * (inner ℝ v z)^2 -
      inner ℝ z z * (inner ℝ v w)^2 :=
  TripleGeometry.cross_gram_identity v w z
private lemma M4.gram_from_q (c : Fin 4 → Pt) (i j k l : Fin 4) :
    4 * (inner ℝ (SphereGeom.cross (c j - c i) (c k - c i)) (c l - c i))^2 =
    gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) := by
  rw [cross_gram_identity, ← q_inner, ← q_inner, ← q_inner,
    inner_from_q, inner_from_q, inner_from_q]
  simp only [gramPoly]
  ring
private lemma M4.retained_set_eq (c : Fin 4 → Pt) (l : Fin 4) :
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
private lemma M4.bulk_patch_counts (c : Fin 4 → Pt) (hn : ∀ l, nRet c l = 1) :
    ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 := by
  intro m
  simp_rw [hn]
  simp
end AreaScope2
section AreaScope3
open M4
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
private lemma M4.two_point_retained_count (p m z : Pt) (a b : ℝ) (hpm : p ≠ m) (hb : 0 < b)
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
private lemma M4.margin_selector (H D Q P A a b : ℝ) (hH : 0 < H) (hD : 0 < D)
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
end AreaScope3
section AreaScope4
open M4
open HardSphereB5.Lean.Geometry.PathCore
set_option maxHeartbeats 1000000
end AreaScope4
section AreaScope5
open M4
open HardSphereB5.Lean.Geometry.PathCore
end AreaScope5
section AreaScope6
open M4
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
private lemma M4.path_s_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) : 0 < s := by
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
private lemma M4.path_Qpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) :
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
private lemma M4.q_nonneg' (c : Fin 4 → Pt) (i j : Fin 4) : 0 ≤ q c i j := by unfold q; positivity
private lemma M4.path_Dpoly_pos (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s) (l : Fin 4) :
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
private lemma M4.norm_sub_base (x y p : Pt) : ‖(x-p)-(y-p)‖ = ‖x-y‖ := by
  congr 1; abel
private lemma M4.triplePts_translate (c : Fin 4 → Pt) (l : Fin 4) :
    triplePts c l = {x | x - c (faceVerts l).1 ∈
      TripleGeometry.triple (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1)} := by
  ext x
  fin_cases l <;>
    simp [triplePts, faceVerts, Fin.forall_fin_succ, TripleGeometry.triple,
      dist_eq_norm, norm_sub_base] <;> tauto
private lemma M4.TG_sq_q (c : Fin 4 → Pt) (i j : Fin 4) : TripleGeometry.sq (c j-c i) = q c i j := by
  exact (q_inner c i j).symm
private lemma M4.TG_sq_diff_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    TripleGeometry.sq ((c j-c i)-(c k-c i)) = q c j k := by
  have he : (c j-c i)-(c k-c i) = c j-c k := by abel
  rw [he, TG_sq_q, q_symm']
private lemma M4.face_TG_D (c : Fin 4 → Pt) (l : Fin 4) :
    TripleGeometry.faceDelta (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) =
    Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 := by
  simp only [TripleGeometry.faceDelta, TG_sq_q, TG_sq_diff_q, Deltaf]
private lemma M4.face_TG_Q (c : Fin 4 → Pt) (l : Fin 4) :
    TripleGeometry.faceQ (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) = Qface c l := by
  simp only [TripleGeometry.faceQ, TG_sq_q, TG_sq_diff_q, Qface, Qf]
private lemma M4.normal_projection_identity (v w z : Pt) (hD : 0 < TripleGeometry.faceDelta v w) :
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
private lemma M4.numerator_identity (v w z : Pt) (hD : TripleGeometry.faceDelta v w ≠ 0) :
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
private theorem M4.nRet_coordinate_selector (c : Fin 4 → Pt) (X Y s : ℝ)
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
end AreaScope6
section AreaScope7
open M4
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
private theorem M4.bulk_incidence {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) :
    (∀ l, nRet c l = 1) ∧ ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 := by
  have hn : ∀ l, nRet c l = 1 := by
    intro l
    rw [nRet_coordinate_selector c X Y s hc (ne_of_gt hP) l,if_pos hP]
  exact ⟨hn,bulk_patch_counts c hn⟩
end AreaScope7
noncomputable section
open MeasureTheory Real SphereGeom
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope8
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 PositiveConvexBoundary)
private structure M4.BulkBoundary.m69 where
  c : Fin 4 → Pt
  X : ℝ
  Y : ℝ
  s : ℝ
  path : IsPathConfig c X Y s
  bulk : 0 < P4poly X Y s
open M4.BulkBoundary
private theorem M4.BulkBoundary.m70 (b : m69) (l : Fin 4) :
    ∃ p : Pt, triplePts b.c l ∩ Kset b.c = {p} := by
  have hn : nRet b.c l = 1 := (bulk_incidence b.path b.bulk).1 l
  by_cases hQ : 0 < Qface b.c l
  · apply Set.ncard_eq_one.mp
    simpa only [nRet, if_pos hQ] using hn
  · simp only [nRet, if_neg hQ] at hn
    exact (Nat.zero_ne_one hn).elim
private def M4.BulkBoundary.m71 (b : m69) (l : Fin 4) : Pt :=
  Classical.choose (m70 b l)
private theorem M4.BulkBoundary.m72 (b : m69) (l : Fin 4) :
    triplePts b.c l ∩ Kset b.c = {m71 b l} :=
  Classical.choose_spec (m70 b l)
private theorem M4.BulkBoundary.m73 (b : m69) (l : Fin 4) :
    m71 b l ∈ triplePts b.c l ∩ Kset b.c := by
  rw [m72]
  exact Set.mem_singleton _
private def M4.BulkBoundary.m74 (i : Fin 4) : Fin 3 → Fin 4 :=
  ![![(1 : Fin 4),2,3], ![0,2,3], ![0,1,3], ![0,1,2]] i
private theorem M4.BulkBoundary.m75 : ∀ (i : Fin 4) (j : Fin 3), m74 i j ≠ i := by decide
private theorem M4.BulkBoundary.m76 : ∀ i : Fin 4, Function.Injective (m74 i) := by decide
private def M4.BulkBoundary.m77 (j : Fin 3) : Fin 3 := ![(0 : Fin 3),2,1] j
private theorem M4.BulkBoundary.m78 : Function.Injective m77 := by decide
private def M4.BulkBoundary.m79 (b : m69) (i : Fin 4) (j : Fin 3) : Fin 4 :=
  let o := m74 i
  if det3 (b.c (o 0) - b.c i) (b.c (o 1) - b.c i) (b.c (o 2) - b.c i) < 0
    then o (m77 j) else o j
private theorem M4.BulkBoundary.m80 (b : m69) (i : Fin 4) (j : Fin 3) :
    m79 b i j ≠ i := by
  dsimp only [m79]
  split_ifs <;> apply m75
private theorem M4.BulkBoundary.m81 (b : m69) (i : Fin 4) :
    Function.Injective (m79 b i) := by
  intro j k h
  dsimp only [m79] at h
  split_ifs at h
  · exact m78 (m76 i h)
  · exact m76 i h
private theorem M4.BulkBoundary.m82 : ∀ j : Fin 3, j ≠ j + 1 := by decide
private theorem M4.BulkBoundary.m83 : ∀ j : Fin 3, j ≠ (j + 1) + 1 := by decide
private def M4.BulkBoundary.m84 (b : m69) (i : Fin 4) (j : Fin 3) : Pt :=
  m71 b (m79 b i (j+1))
private def M4.BulkBoundary.m85 (b : m69) (i : Fin 4) (j : Fin 3) : Pt :=
  m71 b (m79 b i ((j+1)+1))
private theorem M4.BulkBoundary.m86 (b : m69) (i : Fin 4) (j : Fin 3) :
    m85 b i j = m84 b i (j+1) := rfl
private theorem M4.BulkBoundary.m87 (b : m69) (i : Fin 4) (j : Fin 3) :
    m84 b i j ∈
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1 := by
  have h := (m73 b (m79 b i (j+1))).1
  change ∀ m, m ≠ m79 b i (j+1) → dist (m84 b i j) (b.c m) = 1 at h
  have hlabel : m79 b i j ≠ m79 b i (j+1) :=
    fun heq => m82 j (m81 b i heq)
  exact ⟨h i (m80 b i (j+1)).symm, h _ hlabel⟩
private theorem M4.BulkBoundary.m88 (b : m69) (i : Fin 4) (j : Fin 3) :
    m85 b i j ∈
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1 := by
  have h := (m73 b (m79 b i ((j+1)+1))).1
  change ∀ m, m ≠ m79 b i ((j+1)+1) → dist (m85 b i j) (b.c m) = 1 at h
  have hlabel : m79 b i j ≠ m79 b i ((j+1)+1) :=
    fun heq => m83 j (m81 b i heq)
  exact ⟨h i (m80 b i ((j+1)+1)).symm, h _ hlabel⟩
private def M4.BulkBoundary.m89 (b : m69) (i : Fin 4) (j : Fin 3) : Pt :=
  (1/2 : ℝ) • (b.c i + b.c (m79 b i j))
private def M4.BulkBoundary.m90 (b : m69) (i : Fin 4) (j : Fin 3) : ℝ :=
  Real.sqrt (1 - q b.c i (m79 b i j) / 4)
private def M4.BulkBoundary.m91 (b : m69) (i : Fin 4) (j : Fin 3) : Pt :=
  (dist (b.c i) (b.c (m79 b i j)))⁻¹ • (b.c (m79 b i j) - b.c i)
private def M4.BulkBoundary.m92 (b : m69) (i : Fin 4) (j : Fin 3) : Pt :=
  (m90 b i j)⁻¹ • (m84 b i j - m89 b i j)
private def M4.BulkBoundary.m93 (b : m69) (i : Fin 4) (j : Fin 3) : Pt :=
  cross (m91 b i j) (m92 b i j)
private def M4.BulkBoundary.m94 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) : Pt :=
  SphereGeom.circlePt (m89 b i j) (m92 b i j) (m93 b i j) (m90 b i j) t
private def M4.BulkBoundary.m95 (b : m69) (i : Fin 4) (j : Fin 3) : ℝ :=
  let v := m85 b i j - m89 b i j
  let a := atan2 (inner ℝ (m93 b i j) v) (inner ℝ (m92 b i j) v)
  if 0 < a then a else a + 2 * Real.pi
private theorem M4.BulkBoundary.m96 (b : m69) (i : Fin 4) (j : Fin 3) :
    ContDiff ℝ 2 (m94 b i j) := by
  unfold m94 SphereGeom.circlePt
  fun_prop
private def M4.BulkBoundary.m97 (b : m69) (i : Fin 4) (p : Pt) : E2 :=
  let u := p - b.c i
  let d := inner ℝ (m91 b i 0) u
  WithLp.toLp 2 ![inner ℝ (m92 b i 0) u / d, inner ℝ (m93 b i 0) u / d]
private def M4.BulkBoundary.m98 (b : m69) (i : Fin 4) : Set E2 := m97 b i '' patch b.c i
private def M4.BulkBoundary.m99 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) : E2 :=
  m97 b i (m94 b i j t)
private theorem M4.BulkBoundary.m100 (c : Fin 4 → Pt) : IsClosed (Kset c) := by
  unfold Kset body
  exact isClosed_iInter fun n => isClosed_iInter fun _ => Metric.isClosed_closedBall
private theorem M4.BulkBoundary.m101 (c : Fin 4 → Pt) (i : Fin 4) : IsCompact (patch c i) :=
  (isCompact_sphere (c i) 1).inter_right (m100 c)
end AreaScope8
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope9
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 PositiveConvexBoundary)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma M4.BulkBoundary.m102 (hc : IsPathConfig c X Y s) : s < 4 := by
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
private lemma M4.BulkBoundary.m103 (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < q c i j ∧ q c i j < 4 := by
  have hs0 := path_s_pos c X Y s hc
  have hs4 := m102 hc
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
private lemma M4.BulkBoundary.m104 (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < Real.sqrt (1 - q c i j / 4) := by
  apply Real.sqrt_pos.2
  linarith [(m103 hc i j hij).2]
private theorem M4.BulkBoundary.m105 (b : m69) (i : Fin 4) (j : Fin 3) :
    0 < dist (b.c i) (b.c (m79 b i j)) ∧
    dist (b.c i) (b.c (m79 b i j)) < 2 := by
  have h := m103 b.path i (m79 b i j) (m80 b i j).symm
  have hn := dist_nonneg (x := b.c i) (y := b.c (m79 b i j))
  change 0 < dist (b.c i) (b.c (m79 b i j))^2 ∧
    dist (b.c i) (b.c (m79 b i j))^2 < 4 at h
  constructor <;> nlinarith [h.1, h.2]
private theorem M4.BulkBoundary.m106 (b : m69) (i : Fin 4) (j : Fin 3) :
    0 < m90 b i j :=
  m104 b.path i (m79 b i j) (m80 b i j).symm
private theorem M4.BulkBoundary.m107 (b : m69) (i : Fin 4) (j : Fin 3) :
    Gnomonic.CapFrame (m91 b i j) (m92 b i j) (m93 b i j) := by
  let v : Pt := b.c (m79 b i j) - b.c i
  let u : Pt := m84 b i j - b.c i
  let d : ℝ := dist (b.c i) (b.c (m79 b i j))
  let r : ℝ := m90 b i j
  let m : Pt := m84 b i j - m89 b i j
  have hd : 0 < d := (m105 b i j).1
  have hr : 0 < r := m106 b i j
  have hpair := m87 b i j
  have hu : ‖u‖ = 1 := by simpa only [u, Metric.mem_sphere, dist_eq_norm] using hpair.1
  have huw : ‖u-v‖ = 1 := by
    have he : u-v = m84 b i j - b.c (m79 b i j) := by dsimp [u,v]; abel
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
  have hm : m = u - (1/2 : ℝ) • v := by dsimp [m,u,v,m89]; module
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
    have hq := (m103 b.path i (m79 b i j) (m80 b i j).symm).2
    change d^2 < 4 at hq
    linarith
  have haa : inner ℝ (m91 b i j) (m91 b i j) = 1 := by
    change inner ℝ (d⁻¹ • v) (d⁻¹ • v) = 1
    simp only [real_inner_smul_left,real_inner_smul_right,hv]
    field_simp [ne_of_gt hd]
  have he00 : inner ℝ (m92 b i j) (m92 b i j) = 1 := by
    change inner ℝ (r⁻¹ • m) (r⁻¹ • m) = 1
    simp only [real_inner_smul_left,real_inner_smul_right,hmm,← hrr]
    field_simp [ne_of_gt hr]
  have hae0 : inner ℝ (m91 b i j) (m92 b i j) = 0 := by
    change inner ℝ (d⁻¹ • v) (r⁻¹ • m) = 0
    simp only [real_inner_smul_left,real_inner_smul_right,hvm,mul_zero]
  have he11 : inner ℝ (m93 b i j) (m93 b i j) = 1 := by
    have he := TripleGeometry.cross_sq (m91 b i j) (m92 b i j)
    change inner ℝ (m93 b i j) (m93 b i j) = _ at he
    simpa only [TripleGeometry.sq,haa,he00,hae0,mul_one,zero_pow (by decide : (2 : ℕ) ≠ 0),sub_zero] using he
  exact ⟨haa,he00,he11,hae0,
    TripleGeometry.cross_v _ _,TripleGeometry.cross_w _ _⟩
private theorem M4.BulkBoundary.m108 (b : m69) (i : Fin 4) (j : Fin 3) :
    Orthonormal ℝ ![m92 b i j,m93 b i j] := by
  apply orthonormal_iff_ite.mpr
  have F := m107 b i j
  intro a d
  fin_cases a <;> fin_cases d
  · change inner ℝ (m92 b i j) (m92 b i j) = 1
    exact F.e11
  · change inner ℝ (m92 b i j) (m93 b i j) = 0
    exact F.e12
  · change inner ℝ (m93 b i j) (m92 b i j) = 0
    rw [real_inner_comm]
    exact F.e12
  · change inner ℝ (m93 b i j) (m93 b i j) = 1
    exact F.e22
private theorem M4.BulkBoundary.m109 (b : m69) (i : Fin 4) (j : Fin 3) :
    m94 b i j 0 = m84 b i j := by
  have hr : m90 b i j ≠ 0 := ne_of_gt (m106 b i j)
  rw [m94,SphereGeom.circlePt,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,
    add_zero,m92,← mul_smul,mul_inv_cancel₀ hr,one_smul]
  abel
private theorem M4.BulkBoundary.m110 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    m94 b i j t ∈
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1 := by
  have hp : ∀ a : Fin 2,
      inner ℝ (b.c (m79 b i j)-b.c i) (![m92 b i j,m93 b i j] a) = 0 := by
    have F := m107 b i j
    have hdz : (dist (b.c i) (b.c (m79 b i j)))⁻¹ ≠ 0 :=
      inv_ne_zero (ne_of_gt (m105 b i j).1)
    intro a
    fin_cases a
    · have he := F.ae1
      simp only [m91,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
    · have he := F.ae2
      simp only [m91,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
  simpa only [m94,m89,m90,q,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons] using CircleArc.pair_circle_on_spheres
      (b.c i) (b.c (m79 b i j)) ![m92 b i j,m93 b i j]
      (m108 b i j) hp (m105 b i j).2 t
private theorem M4.BulkBoundary.m111 (b : m69) (i : Fin 4) (p : Pt)
    (hp : p ∈ patch b.c i) :
    dist (b.c i) (b.c (m79 b i 0))/2 ≤
      inner ℝ (m91 b i 0) (p-b.c i) := by
  have hball : p ∈ Metric.closedBall (b.c (m79 b i 0)) 1 := by
    have hk := hp.2
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
    exact hk _
  have hb := (CircleArc.ball_iff_inner (b.c i) (b.c (m79 b i 0)) p hp.1).mp hball
  have hd := (m105 b i 0).1
  have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
  have hl : (dist (b.c i) (b.c (m79 b i 0)))⁻¹ *
      (dist (b.c i) (b.c (m79 b i 0))^2/2) =
      dist (b.c i) (b.c (m79 b i 0))/2 := by field_simp
  rw [hl] at hm
  rw [m91,real_inner_smul_left,real_inner_comm]
  exact hm
private theorem M4.BulkBoundary.m112 (b : m69) (i : Fin 4) (p : Pt)
    (hp : p ∈ patch b.c i) : 0 < inner ℝ (m91 b i 0) (p-b.c i) :=
  lt_of_lt_of_le (half_pos (m105 b i 0).1)
    (m111 b i p hp)
private theorem M4.BulkBoundary.m113 (b : m69) (i : Fin 4) :
    ContinuousOn (m97 b i) (patch b.c i) := by
  intro p hp
  have hn : inner ℝ (m91 b i 0) (p-b.c i) ≠ 0 :=
    ne_of_gt (m112 b i p hp)
  apply ContinuousAt.continuousWithinAt
  unfold m97
  dsimp only
  fun_prop (disch := exact hn)
private theorem M4.BulkBoundary.m114 (b : m69) (i : Fin 4) : IsCompact (m98 b i) :=
  (m101 b.c i).image_of_continuousOn (m113 b i)
private theorem M4.BulkBoundary.m115 (b : m69) (i : Fin 4) (j : Fin 3) : 0 < m95 b i j := by
  let z : ℂ := ⟨inner ℝ (m92 b i j) (m85 b i j-m89 b i j),
    inner ℝ (m93 b i j) (m85 b i j-m89 b i j)⟩
  change 0 < (if 0 < Complex.arg z then Complex.arg z else Complex.arg z+2*Real.pi)
  split_ifs with h
  · exact h
  · have hg := Complex.neg_pi_lt_arg z
    linarith [Real.pi_pos]
private theorem M4.BulkBoundary.m116 (b : m69) (i : Fin 4) (j : Fin 3) :
    m95 b i j ≤ 2*Real.pi := by
  let z : ℂ := ⟨inner ℝ (m92 b i j) (m85 b i j-m89 b i j),
    inner ℝ (m93 b i j) (m85 b i j-m89 b i j)⟩
  change (if 0 < Complex.arg z then Complex.arg z else Complex.arg z+2*Real.pi) ≤ _
  split_ifs with h
  · have hg := Complex.arg_le_pi z
    linarith [Real.pi_pos]
  · linarith [le_of_not_gt h]
private theorem M4.BulkBoundary.m117 (m : SphereGeom.E3) (e : Fin 2 → SphereGeom.E3)
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
private theorem M4.BulkBoundary.m118 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    m94 b i j t-b.c i =
      Gnomonic.capArc (m91 b i j) (m92 b i j) (m93 b i j)
        (dist (b.c i) (b.c (m79 b i j))/2) t := by
  let d : ℝ := dist (b.c i) (b.c (m79 b i j))
  have hd : d ≠ 0 := ne_of_gt (m105 b i j).1
  have hv : d • m91 b i j = b.c (m79 b i j)-b.c i := by
    change d • (d⁻¹ • (b.c (m79 b i j)-b.c i)) = _
    rw [← mul_smul,mul_inv_cancel₀ hd,one_smul]
  have hm : m89 b i j-b.c i = (d/2) • m91 b i j := by
    calc
      _ = (1/2 : ℝ) • (b.c (m79 b i j)-b.c i) := by unfold m89; module
      _ = (1/2 : ℝ) • (d • m91 b i j) := by rw [hv]
      _ = _ := by module
  have hr : m90 b i j = Real.sqrt (1-(d/2)^2) := by
    unfold m90 q
    congr 1
    dsimp [d]
    ring
  unfold m94 SphereGeom.circlePt Gnomonic.capArc
  change m89 b i j+m90 b i j •
    (Real.cos t • m92 b i j+Real.sin t • m93 b i j)-b.c i = _
  rw [show m89 b i j+m90 b i j •
    (Real.cos t • m92 b i j+Real.sin t • m93 b i j)-b.c i =
    (m89 b i j-b.c i)+m90 b i j •
    (Real.cos t • m92 b i j+Real.sin t • m93 b i j) by abel,hm,hr]
private def M4.BulkBoundary.m119 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) : Pt :=
  Gnomonic.project (m91 b i 0) (m94 b i j t-b.c i)
end AreaScope9
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope10
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2)
private theorem M4.BulkBoundary.m120 (f : E2 → ℝ)
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
private theorem M4.BulkBoundary.m121 (f : Fin 3 → E2 → ℝ)
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
    rw [m120 (f j) (hc j) (hconc j) w (hw j)] at hij
    change 0 < f j x at hij
    linarith
private theorem M4.BulkBoundary.m122 (n v u w : Pt) (A B C D : ℝ) :
    inner ℝ n (cross (A • v+B • u) (C • w+D • u)) =
      A*C*inner ℝ n (cross v w)+A*D*inner ℝ n (cross v u)+
        B*C*inner ℝ n (cross u w)+B*D*inner ℝ n (cross u u) := by
  simp only [TripleGeometry.inner_coords,TripleGeometry.cross_coords]
  simp
  ring
private theorem M4.BulkBoundary.m123 (n a u w : Pt) :
    inner ℝ n (cross (cross a u) w) =
      inner ℝ n u*inner ℝ a w-inner ℝ n a*inner ℝ u w := by
  simp only [TripleGeometry.inner_coords,TripleGeometry.cross_coords]
  simp
  ring
private theorem M4.BulkBoundary.m124 (n a u w : Pt) :
    (inner ℝ n u)^2*inner ℝ a w-
      inner ℝ n u*inner ℝ n a*inner ℝ u w-
      inner ℝ n u*inner ℝ n w*inner ℝ a u+
      inner ℝ n w*inner ℝ n a*inner ℝ u u-
      inner ℝ n (cross a u)*inner ℝ n (cross u w) =
    inner ℝ n n*(inner ℝ u u*inner ℝ a w-inner ℝ a u*inner ℝ u w) := by
  simp only [TripleGeometry.inner_coords,TripleGeometry.cross_coords]
  simp
  ring
private theorem M4.BulkBoundary.m125 (n a u w : Pt) (h : ℝ)
    (hn : inner ℝ n n = 1) (hu : inner ℝ u u = 1) (hw : inner ℝ w w = 1)
    (hh : 0 ≤ h) (hboundary : inner ℝ a u = h) (hcap : h ≤ inner ℝ a w)
    (hnu : 0 < inner ℝ n u) (hnw : 0 < inner ℝ n w) :
    0 ≤ inner ℝ n (cross (Gnomonic.projectVelocity n u (cross a u))
      (Gnomonic.project n w-Gnomonic.project n u)) := by
  let q := inner ℝ n u
  let p := inner ℝ n w
  let v := cross a u
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
  have hself : inner ℝ n (cross u u) = 0 := by
    simp only [TripleGeometry.inner_coords,TripleGeometry.cross_coords]
    simp
    ring
  have hid : inner ℝ n (cross (Gnomonic.projectVelocity n u (cross a u))
      (Gnomonic.project n w-Gnomonic.project n u)) =
      (inner ℝ a w-h*inner ℝ u w)/(q^2*p) := by
    have hpoly := m124 n a u w
    rw [hn,hu,hboundary] at hpoly
    change q^2*inner ℝ a w-q*inner ℝ n a*inner ℝ u w-
      q*p*h+p*inner ℝ n a*1-inner ℝ n v*inner ℝ n (cross u w) =
      1*(1*inner ℝ a w-h*inner ℝ u w) at hpoly
    calc
      _ = (q^2*inner ℝ a w-q*inner ℝ n a*inner ℝ u w-
          q*p*h+p*inner ℝ n a-inner ℝ n v*inner ℝ n (cross u w))/(q^2*p) := by
        rw [hdiff,Gnomonic.projectVelocity,hqu,hvn,m122,hself]
        rw [m123,m123,hu,hboundary]
        change q⁻¹*p⁻¹*(q*inner ℝ a w-inner ℝ n a*inner ℝ u w)+
          q⁻¹*(-q⁻¹)*(q*h-inner ℝ n a*1)+
          (-inner ℝ n v/q^2)*p⁻¹*inner ℝ n (cross u w)+
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
end AreaScope10
noncomputable section
open scoped Topology ContDiff
section AreaScope11
open M4
open HardSphereB5.Lean.Geometry.PathCore
private def M4.smoothReciprocalDenom (δ t : ℝ) : ℝ :=
  δ / 2 + (t - δ / 2) * Real.smoothTransition ((t - δ / 2) / (δ / 2))
private def M4.smoothReciprocalExtension (δ t : ℝ) : ℝ :=
  (smoothReciprocalDenom δ t)⁻¹
private theorem M4.smoothReciprocalDenom_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
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
private theorem M4.smoothReciprocalDenom_contDiff (δ : ℝ) :
    ContDiff ℝ ∞ (smoothReciprocalDenom δ) := by
  unfold smoothReciprocalDenom
  fun_prop
@[fun_prop]
private theorem M4.smoothReciprocalExtension_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothReciprocalExtension δ) := by
  exact (smoothReciprocalDenom_contDiff δ).inv
    (fun t => (smoothReciprocalDenom_pos δ hδ t).ne')
private theorem M4.smoothReciprocalDenom_eq (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : δ ≤ t) :
    smoothReciprocalDenom δ t = t := by
  have hδ2 : 0 < δ / 2 := by positivity
  have harg : 1 ≤ (t - δ / 2) / (δ / 2) :=
    (one_le_div hδ2).mpr (by linarith)
  simp only [smoothReciprocalDenom, Real.smoothTransition.one_of_one_le harg, mul_one]
  ring
private theorem M4.smoothReciprocalExtension_eq (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : δ ≤ t) :
    smoothReciprocalExtension δ t = 1 / t := by
  simp only [smoothReciprocalExtension, smoothReciprocalDenom_eq δ hδ t ht, one_div]
section Candidate
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
private def M4.rawCircleCandidate (h ρ : ℝ) (e e1 e2 : E) (t : ℝ) : E :=
  h • e + ρ • (Real.cos t • e1 + Real.sin t • e2)
@[fun_prop]
private theorem M4.rawCircleCandidate_contDiff (h ρ : ℝ) (e e1 e2 : E) :
    ContDiff ℝ ∞ (rawCircleCandidate h ρ e e1 e2) := by
  unfold rawCircleCandidate
  fun_prop
private def M4.extendedGnomonicArc (δ h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) (t : ℝ) : H :=
  L (smoothReciprocalExtension δ (inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) •
    rawCircleCandidate h ρ e e1 e2 t - n)
private def M4.gnomonicArcCandidate (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) (t : ℝ) : H :=
  L ((1 / inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) •
    rawCircleCandidate h ρ e e1 e2 t - n)
@[fun_prop]
private theorem M4.extendedGnomonicArc_contDiff (δ : ℝ) (hδ : 0 < δ)
    (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) :
    ContDiff ℝ ∞ (extendedGnomonicArc δ h ρ e e1 e2 n L) := by
  have hu := rawCircleCandidate_contDiff h ρ e e1 e2
  have hd : ContDiff ℝ ∞ (fun t => inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) :=
    contDiff_const.inner ℝ hu
  have hF := (smoothReciprocalExtension_contDiff δ hδ).comp hd
  exact L.contDiff.comp ((hF.smul hu).sub contDiff_const)
private theorem M4.extendedGnomonicArc_contDiff_two (δ : ℝ) (hδ : 0 < δ)
    (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) :
    ContDiff ℝ 2 (extendedGnomonicArc δ h ρ e e1 e2 n L) := by
  exact contDiff_infty.mp (extendedGnomonicArc_contDiff δ hδ h ρ e e1 e2 n L) 2
private theorem M4.extendedGnomonicArc_eq (δ : ℝ) (hδ : 0 < δ)
    (h ρ : ℝ) (e e1 e2 n : E) (L : E →L[ℝ] H) (t : ℝ)
    (ht : δ ≤ inner ℝ n (rawCircleCandidate h ρ e e1 e2 t)) :
    extendedGnomonicArc δ h ρ e e1 e2 n L t =
      gnomonicArcCandidate h ρ e e1 e2 n L t := by
  unfold extendedGnomonicArc gnomonicArcCandidate
  rw [smoothReciprocalExtension_eq δ hδ _ ht]
end Candidate
end AreaScope11
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope12
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2)
private def M4.BulkBoundary.m140 (b : m69) (i : Fin 4) : Pt →L[ℝ] E2 where
  toFun u := WithLp.toLp 2 ![inner ℝ (m92 b i 0) u,inner ℝ (m93 b i 0) u]
  map_add' u v := by ext j; fin_cases j <;> simp [inner_add_right]
  map_smul' a u := by ext j; fin_cases j <;> simp [real_inner_smul_right]
  cont := by fun_prop
private theorem M4.BulkBoundary.m141 (b : m69) (i : Fin 4) (p : Pt) :
    m140 b i (Gnomonic.project (m91 b i 0) (p-b.c i)) =
      m97 b i p := by
  have F := m107 b i 0
  have he0 : inner ℝ (m92 b i 0) (m91 b i 0) = 0 :=
    (real_inner_comm (m91 b i 0) (m92 b i 0)).trans F.ae1
  have he1 : inner ℝ (m93 b i 0) (m91 b i 0) = 0 :=
    (real_inner_comm (m91 b i 0) (m93 b i 0)).trans F.ae2
  have hh : inner ℝ (p-b.c i) (m91 b i 0) =
      inner ℝ (m91 b i 0) (p-b.c i) := real_inner_comm (m91 b i 0) (p-b.c i)
  ext j
  fin_cases j <;>
    simp [m140,Gnomonic.project,m97,inner_sub_right,
      real_inner_smul_right,he0,he1,hh,div_eq_mul_inv,mul_comm]
private def M4.BulkBoundary.m142 (b : m69) (i : Fin 4) (j : Fin 3) : ℝ :=
  dist (b.c i) (b.c (m79 b i j))/2
private def M4.BulkBoundary.m143 (b : m69) (i : Fin 4) : ℝ :=
  dist (b.c i) (b.c (m79 b i 0))/4
private theorem M4.BulkBoundary.m144 (b : m69) (i : Fin 4) : 0 < m143 b i :=
  div_pos (m105 b i 0).1 (by norm_num)
private theorem M4.BulkBoundary.m145 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    rawCircleCandidate (m142 b i j) (m90 b i j)
      (m91 b i j) (m92 b i j) (m93 b i j) t = m94 b i j t-b.c i := by
  have hr : m90 b i j = Real.sqrt (1-(m142 b i j)^2) := by
    unfold m90 m142 q
    congr 1
    ring
  rw [hr]
  change Gnomonic.capArc (m91 b i j) (m92 b i j) (m93 b i j) (m142 b i j) t = _
  exact (m118 b i j t).symm
private def M4.BulkBoundary.m146 (b : m69) (i : Fin 4) (j : Fin 3) : ℝ → E2 :=
  extendedGnomonicArc (m143 b i) (m142 b i j) (m90 b i j)
    (m91 b i j) (m92 b i j) (m93 b i j) (m91 b i 0) (m140 b i)
private theorem M4.BulkBoundary.m147 (b : m69) (i : Fin 4) (j : Fin 3) :
    ContDiff ℝ 2 (m146 b i j) :=
  extendedGnomonicArc_contDiff_two _ (m144 b i) _ _ _ _ _ _ _
private theorem M4.BulkBoundary.m148 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (hm : m143 b i ≤ inner ℝ (m91 b i 0) (m94 b i j t-b.c i)) :
    m146 b i j t = m99 b i j t := by
  have hraw := m145 b i j t
  have he := extendedGnomonicArc_eq (m143 b i) (m144 b i)
    (m142 b i j) (m90 b i j) (m91 b i j) (m92 b i j) (m93 b i j)
    (m91 b i 0) (m140 b i) t (by simpa only [hraw] using hm)
  change extendedGnomonicArc _ _ _ _ _ _ _ _ t = _
  rw [he]
  calc
    _ = m140 b i (Gnomonic.project (m91 b i 0) (m94 b i j t-b.c i)) := by
      unfold gnomonicArcCandidate
      rw [hraw]
      congr 1
      unfold Gnomonic.project
      rw [one_div,real_inner_comm]
    _ = _ := m141 b i (m94 b i j t)
private theorem M4.BulkBoundary.m149 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (hp : m94 b i j t ∈ patch b.c i) :
    m146 b i j t = m99 b i j t := by
  apply m148
  have hl := m111 b i (m94 b i j t) hp
  have hd := (m105 b i 0).1
  unfold m143
  linarith
end AreaScope12
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope13
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 cross2)
private def M4.BulkBoundary.m150 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Pt) (y : E2) : ℝ :=
  inner ℝ v (n+L y)-(‖v‖^2/2)*‖n+L y‖
private theorem M4.BulkBoundary.m151 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Pt) :
    Continuous (m150 n L v) := by
  unfold m150
  fun_prop
private theorem M4.BulkBoundary.m152 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Pt) :
    ConcaveOn ℝ Set.univ (m150 n L v) := by
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
  change a*m150 n L v x+b*m150 n L v y ≤
    m150 n L v (a • x+b • y)
  unfold m150
  rw [hvec]
  simp only [inner_add_right,real_inner_smul_right]
  nlinarith [hn]
private theorem M4.BulkBoundary.m153 (n : Pt) (L : E2 →L[ℝ] Pt) (v : Fin 3 → Pt)
    (w : E2) (hw : ∀ j, 0 < m150 n L (v j) w) :
    frontier {y : E2 | ∀ j, (‖v j‖^2/2)*‖n+L y‖ ≤ inner ℝ (v j) (n+L y)} =
      {y : E2 | (∀ j, (‖v j‖^2/2)*‖n+L y‖ ≤ inner ℝ (v j) (n+L y)) ∧
        ∃ j, (‖v j‖^2/2)*‖n+L y‖ = inner ℝ (v j) (n+L y)} := by
  have h := m121 (fun j => m150 n L (v j))
    (fun j => m151 n L (v j))
    (fun j => m152 n L (v j)) w hw
  have hD : {y : E2 | ∀ j, (‖v j‖^2/2)*‖n+L y‖ ≤ inner ℝ (v j) (n+L y)} =
      {y : E2 | ∀ j, 0 ≤ m150 n L (v j) y} := by
    ext y
    simp only [Set.mem_setOf_eq,m150,sub_nonneg]
  rw [hD,h]
  ext y
  constructor
  · rintro ⟨hy,⟨j,hj⟩⟩
    refine ⟨?_,j,?_⟩
    · simpa only [m150,sub_nonneg] using hy
    · exact (sub_eq_zero.mp hj).symm
  · rintro ⟨hy,⟨j,hj⟩⟩
    refine ⟨?_,j,?_⟩
    · simpa only [m150,sub_nonneg] using hy
    · exact sub_eq_zero.mpr hj.symm
private theorem M4.BulkBoundary.m154 (e n v w : Pt) :
    inner ℝ e v*inner ℝ (cross n e) w-inner ℝ (cross n e) v*inner ℝ e w =
      inner ℝ e e*inner ℝ n (cross v w)-inner ℝ n e*inner ℝ e (cross v w) := by
  simp only [TripleGeometry.inner_coords,TripleGeometry.cross_coords]
  simp
  ring
private theorem M4.BulkBoundary.m155 (b : m69) (i : Fin 4) (v w : Pt) :
    cross2 (m140 b i v) (m140 b i w) =
      inner ℝ (m91 b i 0) (cross v w) := by
  have F := m107 b i 0
  have h := m154 (m92 b i 0) (m91 b i 0) v w
  rw [F.e11,F.ae1] at h
  change inner ℝ (m92 b i 0) v*inner ℝ (m93 b i 0) w-
    inner ℝ (m93 b i 0) v*inner ℝ (m92 b i 0) w = _
  simpa only [m93,one_mul,zero_mul,sub_zero] using h
private theorem M4.BulkBoundary.m156 (b : m69) (i : Fin 4)
    (a u w : Pt) (h : ℝ) (hu : inner ℝ u u = 1) (hw : inner ℝ w w = 1)
    (hh : 0 ≤ h) (hboundary : inner ℝ a u = h) (hcap : h ≤ inner ℝ a w)
    (hnu : 0 < inner ℝ (m91 b i 0) u) (hnw : 0 < inner ℝ (m91 b i 0) w) :
    0 ≤ cross2
      (m140 b i (Gnomonic.projectVelocity (m91 b i 0) u (cross a u)))
      (m140 b i (Gnomonic.project (m91 b i 0) w-Gnomonic.project (m91 b i 0) u)) := by
  rw [m155]
  exact m125 _ a u w h (m107 b i 0).aa hu hw hh hboundary hcap hnu hnw
private theorem M4.BulkBoundary.m157 (a u v : Pt) (A B : ℝ) :
    cross a (A • u+B • v) = A • cross a u+B • cross a v := by
  ext j
  fin_cases j <;> simp [TripleGeometry.cross_coords] <;> ring
private theorem M4.BulkBoundary.m158 (a : Pt) : cross a a = 0 := by
  ext j
  fin_cases j <;> simp [TripleGeometry.cross_coords] <;> ring
private theorem M4.BulkBoundary.m159 (a e : Pt) :
    cross a (cross a e) = inner ℝ a e • a-inner ℝ a a • e := by
  simp only [TripleGeometry.cross_coords,TripleGeometry.inner_coords]
  ext j
  fin_cases j <;> simp <;> ring
private theorem M4.BulkBoundary.m160 (a e : Pt) (h t : ℝ)
    (haa : inner ℝ a a = 1) (hae : inner ℝ a e = 0) :
    Gnomonic.capVelocity e (cross a e) h t =
      cross a (Gnomonic.capArc a e (cross a e) h t) := by
  have he : cross a (cross a e) = -e := by
    rw [m159,hae,haa,zero_smul,one_smul,zero_sub]
  unfold Gnomonic.capVelocity Gnomonic.capArc
  rw [m157,m158,smul_zero,zero_add]
  have hlinear : cross a (Real.cos t • e+Real.sin t • cross a e) =
      Real.cos t • cross a e+Real.sin t • (-e) := by rw [m157,he]
  rw [hlinear]
  module
end AreaScope13
noncomputable section
open SphereGeom
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
section AreaScope14
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
open CircleArc
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
end AreaScope14
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope15
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
private def M4.BulkBoundary.m167 (b : m69) (i : Fin 4) (j : Fin 3) : ℂ :=
  ⟨inner ℝ (m92 b i j) (m85 b i j-m89 b i j),
   inner ℝ (m93 b i j) (m85 b i j-m89 b i j)⟩
private theorem M4.BulkBoundary.m168 (b : m69) (i : Fin 4) (j : Fin 3) :
    ∃ t ∈ Set.Icc (0 : ℝ) (2*Real.pi), m94 b i j t = m85 b i j := by
  have hp : ∀ a : Fin 2,
      inner ℝ (b.c (m79 b i j)-b.c i) (![m92 b i j,m93 b i j] a) = 0 := by
    have F := m107 b i j
    have hdz : (dist (b.c i) (b.c (m79 b i j)))⁻¹ ≠ 0 :=
      inv_ne_zero (ne_of_gt (m105 b i j).1)
    intro a
    fin_cases a
    · have he := F.ae1
      simp only [m91,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
    · have he := F.ae2
      simp only [m91,real_inner_smul_left] at he
      simpa using (mul_eq_zero.mp he).resolve_left hdz
  have hchart := CircleArc.pair_sphere_chart_two
    (b.c i) (b.c (m79 b i j)) ![m92 b i j,m93 b i j]
    (m108 b i j) hp (m105 b i j).1 (m105 b i j).2
  have hmem := m88 b i j
  rw [hchart] at hmem
  simpa only [m94,m89,m90,q,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Set.mem_image] using hmem
private theorem M4.BulkBoundary.m169 (b : m69) (i : Fin 4) (j : Fin 3) :
    ‖m167 b i j‖ = m90 b i j ∧
    m85 b i j = m89 b i j +
      (m167 b i j).re • m92 b i j +
      (m167 b i j).im • m93 b i j := by
  obtain ⟨t,ht,he⟩ := m168 b i j
  have F := m107 b i j
  have h01 : inner ℝ (m93 b i j) (m92 b i j) = 0 := by
    rw [real_inner_comm]; exact F.e12
  have hvec : m85 b i j-m89 b i j =
      (m90 b i j*Real.cos t) • m92 b i j +
      (m90 b i j*Real.sin t) • m93 b i j := by
    rw [← he,m94,SphereGeom.circlePt]
    simp only [smul_add,smul_smul]
    abel
  have hre : (m167 b i j).re = m90 b i j*Real.cos t := by
    change inner ℝ (m92 b i j) (m85 b i j-m89 b i j) = _
    rw [hvec]
    simp only [inner_add_right,real_inner_smul_right,
      F.e11,F.e12,mul_one,mul_zero,add_zero]
  have him : (m167 b i j).im = m90 b i j*Real.sin t := by
    change inner ℝ (m93 b i j) (m85 b i j-m89 b i j) = _
    rw [hvec]
    simp only [inner_add_right,real_inner_smul_right,
      F.e22,h01,mul_one,mul_zero,zero_add]
  have hn : ‖m167 b i j‖^2 = (m90 b i j)^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,hre,him]
    nlinarith [Real.sin_sq_add_cos_sq t]
  constructor
  · nlinarith [norm_nonneg (m167 b i j),(m106 b i j)]
  · rw [hre,him,← he,m94,SphereGeom.circlePt]
    simp only [smul_add,smul_smul]
    abel
private theorem M4.BulkBoundary.m170 (b : m69) (i : Fin 4) (j : Fin 3) :
    m94 b i j (m95 b i j) = m85 b i j := by
  have H := m169 b i j
  have hc : m90 b i j*Real.cos (m95 b i j) = (m167 b i j).re := by
    have hh := Complex.norm_mul_cos_arg (m167 b i j)
    rw [H.1] at hh
    change m90 b i j*Real.cos
      (if 0 < (m167 b i j).arg then (m167 b i j).arg
        else (m167 b i j).arg+2*Real.pi) = _
    split_ifs <;> simpa only [Real.cos_add_two_pi] using hh
  have hs : m90 b i j*Real.sin (m95 b i j) = (m167 b i j).im := by
    have hh := Complex.norm_mul_sin_arg (m167 b i j)
    rw [H.1] at hh
    change m90 b i j*Real.sin
      (if 0 < (m167 b i j).arg then (m167 b i j).arg
        else (m167 b i j).arg+2*Real.pi) = _
    split_ifs <;> simpa only [Real.sin_add_two_pi] using hh
  rw [m94,SphereGeom.circlePt]
  simp only [smul_add,smul_smul,hc,hs]
  simpa only [add_assoc] using H.2.symm
private theorem M4.BulkBoundary.m171 (b : m69) (i : Fin 4) (j : Fin 3) :
    m94 b i j (m95 b i j) = m94 b i (j+1) 0 := by
  rw [m170,m109,m86]
private theorem M4.BulkBoundary.m172 (b : m69) (i : Fin 4) (j : Fin 3)
    (hne : m84 b i j ≠ m85 b i j) :
    m95 b i j < 2*Real.pi := by
  have hh := m116 b i j
  apply lt_of_le_of_ne hh
  intro he
  apply hne
  have hc := m170 b i j
  rw [he,m94,SphereGeom.circlePt,Real.cos_two_pi,Real.sin_two_pi,
    one_smul,zero_smul,add_zero] at hc
  have h0 := m109 b i j
  rw [m94,SphereGeom.circlePt,Real.cos_zero,Real.sin_zero,
    one_smul,zero_smul,add_zero] at h0
  exact h0.symm.trans hc
private theorem M4.BulkBoundary.m173 (B : m69) (x : Pt)
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
private theorem M4.BulkBoundary.m174 (b : m69) : Function.Injective (m71 b) := by
  intro l k he
  by_contra hne
  apply m173 b (m71 b l)
  intro m
  by_cases hml : m = l
  · subst m
    have hk := (m73 b k).1
    change ∀ a, a ≠ k → dist (m71 b k) (b.c a) = 1 at hk
    rw [he]
    exact hk l hne
  · have hl := (m73 b l).1
    change ∀ a, a ≠ l → dist (m71 b l) (b.c a) = 1 at hl
    exact hl m hml
private theorem M4.BulkBoundary.m175 (b : m69) (i : Fin 4) (j : Fin 3) :
    m84 b i j ≠ m85 b i j := by
  intro he
  have ho := m174 b he
  exact m82 (j+1) (m81 b i ho)
private theorem M4.BulkBoundary.m176 (b : m69) (i : Fin 4) (j : Fin 3) :
    m95 b i j < 2*Real.pi :=
  m172 b i j (m175 b i j)
end AreaScope15
noncomputable section
open Real SphereGeom
section AreaScope16
private abbrev HardSphereB5.Lean.Geometry.PathCore.BulkSOC.E2 := EuclideanSpace ℝ (Fin 2)
open HardSphereB5.Lean.Geometry.PathCore.BulkSOC
private theorem HardSphereB5.Lean.Geometry.PathCore.BulkSOC.norm_affine_region_convex {ι : Type*} (n : E3) (L : E2 →ₗ[ℝ] E3) (v : ι → E3) :
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
private theorem HardSphereB5.Lean.Geometry.PathCore.BulkSOC.unit_ball_iff_norm_affine (n u v : E3) (L : E2 →ₗ[ℝ] E3) (y : E2)
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
end AreaScope16
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope17
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2)
private theorem M4.BulkBoundary.full_frame_on (a e f : Pt) (F : Gnomonic.CapFrame a e f) :
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
private def M4.BulkBoundary.m181 (b : m69) (i : Fin 4) : OrthonormalBasis (Fin 3) ℝ Pt :=
  OrthonormalBasis.mk (full_frame_on _ _ _ (m107 b i 0))
    ((full_frame_on _ _ _ (m107 b i 0)).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [HardSphereB5.Lean.Pt, SphereGeom.E3, finrank_euclideanSpace])).ge
private theorem M4.BulkBoundary.m182 (b : m69) (i : Fin 4) (u : Pt) :
    inner ℝ (m92 b i 0) u • m92 b i 0 +
      inner ℝ (m93 b i 0) u • m93 b i 0 +
      inner ℝ (m91 b i 0) u • m91 b i 0 = u := by
  have h := (m181 b i).sum_repr' u
  simpa only [m181,OrthonormalBasis.coe_mk,Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using h
private def M4.BulkBoundary.m183 (b : m69) (i : Fin 4) : E2 →L[ℝ] Pt where
  toFun y := y 0 • m92 b i 0 + y 1 • m93 b i 0
  map_add' x y := by simp only [PiLp.add_apply,add_smul]; module
  map_smul' a y := by
    change (a*y 0) • m92 b i 0+(a*y 1) • m93 b i 0 =
      a • (y 0 • m92 b i 0+y 1 • m93 b i 0)
    simp only [smul_add,smul_smul]
  cont := by fun_prop
private def M4.BulkBoundary.m184 (b : m69) (i : Fin 4) (y : E2) : Pt :=
  m91 b i 0 + m183 b i y
private def M4.BulkBoundary.m185 (b : m69) (i : Fin 4) (y : E2) : Pt :=
  ‖m184 b i y‖⁻¹ • m184 b i y
private def M4.BulkBoundary.m186 (b : m69) (i : Fin 4) : Set E2 :=
  {y | ∀ j : Fin 3, (‖b.c (m79 b i j)-b.c i‖^2/2)*‖m184 b i y‖ ≤
    inner ℝ (b.c (m79 b i j)-b.c i) (m184 b i y)}
private theorem M4.BulkBoundary.m187 (b : m69) (i : Fin 4) (y : E2) :
    inner ℝ (m91 b i 0) (m184 b i y) = 1 := by
  change inner ℝ (m91 b i 0)
    (m91 b i 0+(y 0 • m92 b i 0+y 1 • m93 b i 0)) = 1
  simp only [inner_add_right,real_inner_smul_right,(m107 b i 0).aa,
    (m107 b i 0).ae1,(m107 b i 0).ae2,mul_zero,add_zero]
private theorem M4.BulkBoundary.m188 (b : m69) (i : Fin 4) (y : E2) :
    inner ℝ (m92 b i 0) (m184 b i y) = y 0 := by
  have F:=m107 b i 0
  have he : inner ℝ (m92 b i 0) (m91 b i 0) = 0 := by rw [real_inner_comm];exact F.ae1
  change inner ℝ (m92 b i 0)
    (m91 b i 0+(y 0 • m92 b i 0+y 1 • m93 b i 0)) = y 0
  simp only [inner_add_right,real_inner_smul_right,he,F.e11,F.e12,
    mul_zero,mul_one,zero_add,add_zero]
private theorem M4.BulkBoundary.m189 (b : m69) (i : Fin 4) (y : E2) :
    inner ℝ (m93 b i 0) (m184 b i y) = y 1 := by
  have F:=m107 b i 0
  have he : inner ℝ (m93 b i 0) (m91 b i 0) = 0 := by rw [real_inner_comm];exact F.ae2
  have hf : inner ℝ (m93 b i 0) (m92 b i 0) = 0 := by rw [real_inner_comm];exact F.e12
  change inner ℝ (m93 b i 0)
    (m91 b i 0+(y 0 • m92 b i 0+y 1 • m93 b i 0)) = y 1
  simp only [inner_add_right,real_inner_smul_right,he,hf,F.e22,
    mul_zero,mul_one,zero_add,add_zero]
private theorem M4.BulkBoundary.m190 (b : m69) (i : Fin 4) (y : E2) : m184 b i y ≠ 0 := by
  intro he
  have h:=m187 b i y
  rw [he,inner_zero_right] at h
  norm_num at h
private theorem M4.BulkBoundary.m191 (b : m69) (i : Fin 4) (y : E2) : 0 < ‖m184 b i y‖ :=
  norm_pos_iff.mpr (m190 b i y)
private theorem M4.BulkBoundary.m192 (b : m69) (i : Fin 4) (y : E2) : ‖m185 b i y‖ = 1 := by
  rw [m185,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (m191 b i y).ne']
private theorem M4.BulkBoundary.m193 (b : m69) (i : Fin 4) (y : E2) :
    inner ℝ (m91 b i 0) (m185 b i y) = ‖m184 b i y‖⁻¹ := by
  rw [m185,real_inner_smul_right,m187,mul_one]
private theorem M4.BulkBoundary.m194 (b : m69) (i : Fin 4) (y : E2) :
    m97 b i (b.c i+m185 b i y) = y := by
  have ht : (‖m184 b i y‖⁻¹) ≠ 0 := inv_ne_zero (m191 b i y).ne'
  ext k
  fin_cases k
  · change inner ℝ (m92 b i 0) (b.c i+m185 b i y-b.c i) /
      inner ℝ (m91 b i 0) (b.c i+m185 b i y-b.c i) = y 0
    rw [add_sub_cancel_left,m193,m185,real_inner_smul_right,m188]
    exact mul_div_cancel_left₀ (y 0) ht
  · change inner ℝ (m93 b i 0) (b.c i+m185 b i y-b.c i) /
      inner ℝ (m91 b i 0) (b.c i+m185 b i y-b.c i) = y 1
    rw [add_sub_cancel_left,m193,m185,real_inner_smul_right,m189]
    exact mul_div_cancel_left₀ (y 1) ht
private theorem M4.BulkBoundary.m195 (b : m69) (i : Fin 4) (p : Pt)
    (ht : inner ℝ (m91 b i 0) (p-b.c i) ≠ 0) :
    m184 b i (m97 b i p) =
      (inner ℝ (m91 b i 0) (p-b.c i))⁻¹ • (p-b.c i) := by
  have h:=m182 b i (p-b.c i)
  calc
    _ = (inner ℝ (m91 b i 0) (p-b.c i))⁻¹ •
        (inner ℝ (m92 b i 0) (p-b.c i) • m92 b i 0+
         inner ℝ (m93 b i 0) (p-b.c i) • m93 b i 0+
         inner ℝ (m91 b i 0) (p-b.c i) • m91 b i 0) := by
      change m91 b i 0+
        ((inner ℝ (m92 b i 0) (p-b.c i)/inner ℝ (m91 b i 0) (p-b.c i)) • m92 b i 0+
         (inner ℝ (m93 b i 0) (p-b.c i)/inner ℝ (m91 b i 0) (p-b.c i)) • m93 b i 0) = _
      simp only [smul_add,smul_smul,div_eq_mul_inv,inv_mul_cancel₀ ht,one_smul]
      module
    _ = _ := by rw [h]
private theorem M4.BulkBoundary.m196 (b : m69) (i k : Fin 4) (hki : k ≠ i) :
    ∃ j, m79 b i j = k := by
  have ho : ∃ j, m74 i j = k := by
    fin_cases i <;> fin_cases k <;> simp_all [m74] <;> decide
  rcases ho with ⟨j,hj⟩
  unfold m79
  dsimp only
  split_ifs
  · have hf : Function.Surjective m77 := (Finite.injective_iff_surjective).mp m78
    rcases hf j with ⟨j',hj'⟩
    exact ⟨j',by rw [hj'];exact hj⟩
  · exact ⟨j,hj⟩
private theorem M4.BulkBoundary.m197 (b : m69) (i : Fin 4) (y : E2) :
    m184 b i y = (inner ℝ (m91 b i 0) (m185 b i y))⁻¹ • m185 b i y := by
  rw [m193,inv_inv,m185,← mul_smul,
    mul_inv_cancel₀ (m191 b i y).ne',one_smul]
private theorem M4.BulkBoundary.m198 (b : m69) (i : Fin 4) (y : E2)
    (hy : y ∈ m186 b i) : b.c i+m185 b i y ∈ patch b.c i := by
  have hu:=m192 b i y
  have ht : 0 < inner ℝ (m91 b i 0) (m185 b i y) := by
    rw [m193];exact inv_pos.mpr (m191 b i y)
  constructor
  · change dist (b.c i+m185 b i y) (b.c i) = 1
    simpa only [dist_eq_norm,add_sub_cancel_left] using hu
  · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
    intro k
    change dist (b.c i+m185 b i y) (b.c k) ≤ 1
    by_cases hki : k = i
    · subst k
      simpa only [dist_eq_norm,add_sub_cancel_left,hu] using (le_refl (1:ℝ))
    · obtain ⟨j,hj⟩:=m196 b i k hki
      have hm : (‖b.c k-b.c i‖^2/2)*‖m184 b i y‖ ≤
        inner ℝ (b.c k-b.c i) (m184 b i y) := by
        have hh:=hy j
        simpa only [hj] using hh
      have hb:= (BulkSOC.unit_ball_iff_norm_affine (m91 b i 0) (m185 b i y)
        (b.c k-b.c i) (m183 b i).toLinearMap y
        (inner ℝ (m91 b i 0) (m185 b i y)) hu ht
        (m197 b i y)).mpr hm
      have hd : dist (m185 b i y) (b.c k-b.c i) =
          dist (b.c i+m185 b i y) (b.c k) := by
        rw [dist_eq_norm,dist_eq_norm]
        congr 1
        abel
      rwa [hd] at hb
private theorem M4.BulkBoundary.m199 (b : m69) (i : Fin 4) (p : Pt)
    (hp : p ∈ patch b.c i) : m97 b i p ∈ m186 b i := by
  have hu : ‖p-b.c i‖ = 1 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
  have ht:=m112 b i p hp
  intro j
  have hb : dist (p-b.c i) (b.c (m79 b i j)-b.c i) ≤ 1 := by
    have hk:=hp.2
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
    have h:=hk (m79 b i j)
    change dist p (b.c (m79 b i j)) ≤ 1 at h
    have he : dist (p-b.c i) (b.c (m79 b i j)-b.c i) =
        dist p (b.c (m79 b i j)) := by
      rw [dist_eq_norm,dist_eq_norm];congr 1;abel
    rwa [he]
  exact (BulkSOC.unit_ball_iff_norm_affine (m91 b i 0) (p-b.c i)
    (b.c (m79 b i j)-b.c i) (m183 b i).toLinearMap
    (m97 b i p) (inner ℝ (m91 b i 0) (p-b.c i)) hu ht
    (m195 b i p ht.ne')).mp hb
private theorem M4.BulkBoundary.m200 (b : m69) (i : Fin 4) : m98 b i = m186 b i := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact m199 b i p hp
  · intro hy
    exact ⟨b.c i+m185 b i y, m198 b i y hy, m194 b i y⟩
private theorem M4.BulkBoundary.m201 (b : m69) (i : Fin 4) : Convex ℝ (m98 b i) := by
  rw [m200]
  exact BulkSOC.norm_affine_region_convex (m91 b i 0) (m183 b i).toLinearMap
    (fun j : Fin 3 => b.c (m79 b i j)-b.c i)
private theorem M4.BulkBoundary.m202 (b : m69) (l : Fin 4) :
    dist (m71 b l) (b.c l) < 1 := by
  have hk:=(m73 b l).2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
  have hl : dist (m71 b l) (b.c l) ≤ 1 := hk l
  apply lt_of_le_of_ne hl
  intro he
  apply m173 b (m71 b l)
  intro m
  by_cases hml : m = l
  · subst m;exact he
  · exact (m73 b l).1 m hml
private def M4.BulkBoundary.m203 (b : m69) (i : Fin 4) (j : Fin 3) : Pt :=
  m71 b (m79 b i j)-b.c i
private theorem M4.BulkBoundary.m204 (b : m69) (i : Fin 4) (j : Fin 3) :
    ‖m203 b i j‖ = 1 := by
  have h:=(m73 b (m79 b i j)).1 i (m80 b i j).symm
  simpa only [dist_eq_norm,m203] using h
private theorem M4.BulkBoundary.m205 (b : m69) (i : Fin 4) (j k : Fin 3) :
    ‖b.c (m79 b i j)-b.c i‖^2/2 ≤
      inner ℝ (b.c (m79 b i j)-b.c i) (m203 b i k) := by
  have h:=(m73 b (m79 b i k)).2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at h
  have hb : dist (m71 b (m79 b i k)) (b.c (m79 b i j)) ≤ 1 := h _
  have ht : m203 b i k-(b.c (m79 b i j)-b.c i) =
      m71 b (m79 b i k)-b.c (m79 b i j) := by unfold m203;abel
  have he:=norm_sub_sq_real (m203 b i k) (b.c (m79 b i j)-b.c i)
  rw [m204,real_inner_comm] at he
  have hh : ‖m203 b i k-(b.c (m79 b i j)-b.c i)‖ ≤ 1 := by
    rw [ht];simpa only [dist_eq_norm] using hb
  nlinarith [norm_nonneg (m203 b i k-(b.c (m79 b i j)-b.c i))]
private theorem M4.BulkBoundary.m206 (b : m69) (i : Fin 4) (j : Fin 3) :
    ‖b.c (m79 b i j)-b.c i‖^2/2 <
      inner ℝ (b.c (m79 b i j)-b.c i) (m203 b i j) := by
  have hb:=m202 b (m79 b i j)
  have ht : m203 b i j-(b.c (m79 b i j)-b.c i) =
      m71 b (m79 b i j)-b.c (m79 b i j) := by unfold m203;abel
  have he:=norm_sub_sq_real (m203 b i j) (b.c (m79 b i j)-b.c i)
  rw [m204,real_inner_comm] at he
  have hh : ‖m203 b i j-(b.c (m79 b i j)-b.c i)‖ < 1 := by
    rw [ht];simpa only [dist_eq_norm] using hb
  nlinarith [norm_nonneg (m203 b i j-(b.c (m79 b i j)-b.c i))]
private def M4.BulkBoundary.m207 (b : m69) (i : Fin 4) : Pt := ∑ j : Fin 3, m203 b i j
private theorem M4.BulkBoundary.m208 (b : m69) (i : Fin 4) : ‖m207 b i‖ ≤ 3 := by
  apply (norm_sum_le _ _).trans
  simp only [m204,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num
private theorem M4.BulkBoundary.m209 (b : m69) (i : Fin 4) (j : Fin 3) :
    3*(‖b.c (m79 b i j)-b.c i‖^2/2) <
      inner ℝ (b.c (m79 b i j)-b.c i) (m207 b i) := by
  have h:=Finset.sum_lt_sum (fun k (_ : k ∈ Finset.univ) => m205 b i j k)
    ⟨j,Finset.mem_univ _,m206 b i j⟩
  simpa only [m207,inner_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Nat.cast_ofNat,nsmul_eq_mul] using h
private theorem M4.BulkBoundary.m210 (b : m69) (i : Fin 4) : m207 b i ≠ 0 := by
  intro he
  have h:=m209 b i 0
  rw [he,inner_zero_right] at h
  have hn : 0 ≤ 3*(‖b.c (m79 b i 0)-b.c i‖^2/2) := by positivity
  linarith
private def M4.BulkBoundary.m211 (b : m69) (i : Fin 4) : Pt :=
  ‖m207 b i‖⁻¹ • m207 b i
private theorem M4.BulkBoundary.m212 (b : m69) (i : Fin 4) : ‖m211 b i‖ = 1 := by
  rw [m211,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ ‖m207 b i‖⁻¹),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (m210 b i))]
private theorem M4.BulkBoundary.m213 (b : m69) (i : Fin 4) (j : Fin 3) :
    ‖b.c (m79 b i j)-b.c i‖^2/2 <
      inner ℝ (b.c (m79 b i j)-b.c i) (m211 b i) := by
  have hn : 0 < ‖m207 b i‖ := norm_pos_iff.mpr (m210 b i)
  have hle:=mul_le_mul_of_nonneg_right (m208 b i)
    (show 0 ≤ ‖b.c (m79 b i j)-b.c i‖^2/2 by positivity)
  have hlt:=lt_of_le_of_lt hle (m209 b i j)
  have h:=mul_lt_mul_of_pos_left hlt (inv_pos.mpr hn)
  rw [m211,real_inner_smul_right]
  calc
    _ = ‖m207 b i‖⁻¹ * (‖m207 b i‖*(‖b.c (m79 b i j)-b.c i‖^2/2)) := by
      rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]
    _ < _ := h
private theorem M4.BulkBoundary.m214 (b : m69) (i : Fin 4) (u : Pt) (hu : ‖u‖ = 1)
    (hcap : ∀ j : Fin 3, ‖b.c (m79 b i j)-b.c i‖^2/2 ≤
      inner ℝ (b.c (m79 b i j)-b.c i) u) : b.c i+u ∈ patch b.c i := by
  constructor
  · simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hu
  · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
    intro k
    change dist (b.c i+u) (b.c k) ≤ 1
    by_cases hki:k=i
    · subst k;simpa only [dist_eq_norm,add_sub_cancel_left,hu] using (le_refl (1:ℝ))
    · obtain ⟨j,hj⟩:=m196 b i k hki
      have hb:=hcap j
      rw [hj] at hb
      have he:=norm_sub_sq_real u (b.c k-b.c i)
      rw [hu,real_inner_comm] at he
      have hd : dist (b.c i+u) (b.c k) = ‖u-(b.c k-b.c i)‖ := by
        rw [dist_eq_norm];congr 1;abel
      rw [hd]
      nlinarith [norm_nonneg (u-(b.c k-b.c i))]
private theorem M4.BulkBoundary.m215 (b : m69) (i : Fin 4) :
    b.c i+m211 b i ∈ patch b.c i :=
  m214 b i _ (m212 b i)
    (fun j => (m213 b i j).le)
private theorem M4.BulkBoundary.m216 (b : m69) (i : Fin 4) :
    ∃ y : E2, ∀ j : Fin 3, 0 < m150 (m91 b i 0) (m183 b i)
      (b.c (m79 b i j)-b.c i) y := by
  let p:Pt:=b.c i+m211 b i
  have hp:p∈patch b.c i:=m215 b i
  have ht:=m112 b i p hp
  have hre:m184 b i (m97 b i p)=
      (inner ℝ (m91 b i 0) (p-b.c i))⁻¹ • m211 b i := by
    rw [m195 b i p ht.ne']
    simp only [p,add_sub_cancel_left]
  refine ⟨m97 b i p,?_⟩
  intro j
  have h:=mul_lt_mul_of_pos_left (m213 b i j) (inv_pos.mpr ht)
  change 0 < inner ℝ (b.c (m79 b i j)-b.c i) (m184 b i (m97 b i p))-
    (‖b.c (m79 b i j)-b.c i‖^2/2)*‖m184 b i (m97 b i p)‖
  rw [hre,real_inner_smul_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le),
    m212,mul_one]
  nlinarith [h]
private theorem M4.BulkBoundary.m217 (b : m69) (i : Fin 4) :
    (interior (m98 b i)).Nonempty := by
  obtain ⟨y,hy⟩:=m216 b i
  let A:Set E2:= {x | ∀ j : Fin 3, 0 < m150 (m91 b i 0) (m183 b i)
    (b.c (m79 b i j)-b.c i) x}
  have hOpen:IsOpen A:=by
    have he:A=⋂j:Fin 3,{x | 0 < m150 (m91 b i 0) (m183 b i)
      (b.c (m79 b i j)-b.c i) x}:=by ext x;simp only [A,Set.mem_setOf_eq,Set.mem_iInter]
    rw [he]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (m151 _ _ _))
  have hsub:A ⊆ m98 b i:=by
    rw [m200]
    intro x hx j
    exact sub_nonneg.mp (hx j).le
  exact ⟨y,interior_maximal hsub hOpen hy⟩
private theorem M4.BulkBoundary.m218 (b : m69) (i : Fin 4) (p : Pt)
    (hp:p∈patch b.c i) : m185 b i (m97 b i p)=p-b.c i := by
  have hu:‖p-b.c i‖=1:=by simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
  have ht:=m112 b i p hp
  rw [m185,m195 b i p ht.ne',norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr ht.le),hu,mul_one,inv_inv,
    ←mul_smul,mul_inv_cancel₀ ht.ne',one_smul]
private theorem M4.BulkBoundary.m219 (b : m69) (i : Fin 4) :
    Set.InjOn (m97 b i) (patch b.c i) := by
  intro p hp q hq he
  have h:=congrArg (m185 b i) he
  rw [m218 b i p hp,m218 b i q hq] at h
  have hh:=congrArg (fun x : Pt => x+b.c i) h
  simpa only [sub_add_cancel] using hh
private theorem M4.BulkBoundary.m220 (b : m69) (i : Fin 4) (j : Fin 3) (y : E2) :
    (‖b.c (m79 b i j)-b.c i‖^2/2)*‖m184 b i y‖ =
      inner ℝ (b.c (m79 b i j)-b.c i) (m184 b i y) ↔
    b.c i+m185 b i y ∈ Metric.sphere (b.c (m79 b i j)) 1 := by
  let v:Pt:=b.c (m79 b i j)-b.c i
  let u:Pt:=m185 b i y
  let R:ℝ:=‖m184 b i y‖
  have hR:0<R:=m191 b i y
  have hu:‖u‖=1:=m192 b i y
  have he:dist (b.c i+u) (b.c (m79 b i j))^2=
      1-2*inner ℝ v u+‖v‖^2:=by
    have hv:(b.c i+u)-b.c (m79 b i j)=u-v:=by dsimp [v];abel
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,real_inner_comm u v]
    ring
  have hid:inner ℝ v u=R⁻¹*inner ℝ v (m184 b i y):=by
    change inner ℝ v (R⁻¹ • m184 b i y)=_
    rw [real_inner_smul_right]
  have hmul:R*inner ℝ v u=inner ℝ v (m184 b i y):=by
    rw [hid,←mul_assoc,mul_inv_cancel₀ hR.ne',one_mul]
  change (‖v‖^2/2)*R=inner ℝ v (m184 b i y) ↔ _
  simp only [Metric.mem_sphere]
  constructor
  · intro h
    have hc:‖v‖^2/2=inner ℝ v u:=by nlinarith [hmul]
    nlinarith [dist_nonneg (x:=b.c i+u) (y:=b.c (m79 b i j))]
  · intro h
    have hc:‖v‖^2/2=inner ℝ v u:=by nlinarith [he]
    calc _ = R*inner ℝ v u := by rw [hc];ring
         _ = _ := hmul
private theorem M4.BulkBoundary.m221 (b : m69) (i : Fin 4) :
    frontier (m98 b i) = {y : E2 | y ∈ m186 b i ∧
      ∃ j : Fin 3, (‖b.c (m79 b i j)-b.c i‖^2/2)*‖m184 b i y‖ =
        inner ℝ (b.c (m79 b i j)-b.c i) (m184 b i y)} := by
  obtain ⟨w,hw⟩:=m216 b i
  rw [m200]
  exact m153 (m91 b i 0) (m183 b i)
    (fun j : Fin 3 => b.c (m79 b i j)-b.c i) w hw
private theorem M4.BulkBoundary.m222 (b : m69) (i : Fin 4) :
    frontier (m98 b i) = ⋃ j : Fin 3, m97 b i ''
      (patch b.c i ∩ Metric.sphere (b.c (m79 b i j)) 1) := by
  rw [m221]
  ext y
  simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_image,Set.mem_inter_iff]
  constructor
  · rintro ⟨hy,j,hj⟩
    refine ⟨j,b.c i+m185 b i y,⟨m198 b i y hy,?_⟩,
      m194 b i y⟩
    exact (m220 b i j y).mp hj
  · rintro ⟨j,p,⟨hp,hj⟩,rfl⟩
    refine ⟨m199 b i p hp,j,?_⟩
    apply (m220 b i j (m97 b i p)).mpr
    have he:b.c i+m185 b i (m97 b i p)=p:=by
      rw [m218 b i p hp];abel
    rwa [he]
private def M4.BulkBoundary.m223 (b : m69) (i : Fin 4) : Pt ≃ₗᵢ[ℝ] Pt := (m181 b i).repr.symm
private theorem M4.BulkBoundary.m224 (b : m69) (i : Fin 4) (u:Pt) :
    (m223 b i).symm u = WithLp.toLp 2 ![inner ℝ (m92 b i 0) u,
      inner ℝ (m93 b i 0) u,inner ℝ (m91 b i 0) u] := by
  ext j
  simp only [m223,LinearIsometryEquiv.symm_symm,
    OrthonormalBasis.repr_apply_apply,m181,OrthonormalBasis.coe_mk]
  fin_cases j <;> rfl
private theorem M4.BulkBoundary.m225 (b : m69) (i : Fin 4) (p:Pt) :
    m97 b i p=Gnomonic.chartFrame (m223 b i) (p-b.c i) := by
  rw [Gnomonic.chartFrame,m224]
  rfl
private theorem M4.BulkBoundary.m226 (b : m69) (i : Fin 4) (y:E2) :
    m223 b i (WithLp.toLp 2 ![y 0,y 1,1])=m184 b i y := by
  have h:=(m181 b i).sum_repr_symm (WithLp.toLp 2 ![y 0,y 1,1])
  simp only [m181,OrthonormalBasis.coe_mk,Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons,one_smul] at h
  calc
    _ = y 0 • m92 b i 0+y 1 • m93 b i 0+m91 b i 0 := by
      simpa only [m223,m181] using h.symm
    _ = _ := by change _=m91 b i 0+(y 0 • m92 b i 0+y 1 • m93 b i 0);abel
private theorem M4.BulkBoundary.m227 (b : m69) (i : Fin 4) (y:E2) :
    ‖m184 b i y‖=Real.sqrt (1+‖y‖^2) := by
  rw [←m226,(m223 b i).norm_map]
  have hs:‖WithLp.toLp 2 ![y 0,y 1,1]‖^2=1+‖y‖^2:=by
    simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
    simp
    ring
  have hr:0≤1+‖y‖^2:=by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 ![y 0,y 1,1] : Pt),Real.sqrt_nonneg (1+‖y‖^2),Real.sq_sqrt hr]
private theorem M4.BulkBoundary.m228 (b : m69) (i : Fin 4) (y:E2) :
    m185 b i y=Gnomonic.inverseFrame (m223 b i) y := by
  rw [m185,m227,Gnomonic.inverseFrame,map_smul,m226]
private def M4.BulkBoundary.m229 (b : m69) (i : Fin 4) : Set Pt :=
  (fun p:Pt=>p-b.c i) '' patch b.c i
private theorem M4.BulkBoundary.m230 (b : m69) (i : Fin 4) :
    m229 b i ⊆ Gnomonic.hemisphereFrame (m223 b i) := by
  rintro u ⟨p,hp,rfl⟩
  constructor
  · simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
  · rw [m224]
    exact m112 b i p hp
private theorem M4.BulkBoundary.m231 (b : m69) (i : Fin 4) :
    m98 b i=Gnomonic.chartFrame (m223 b i) '' m229 b i := by
  unfold m98 m229
  rw [←Set.image_comp]
  congr 1
  funext p
  exact m225 b i p
private theorem M4.BulkBoundary.m232 (b : m69) (i : Fin 4) :
    MeasurableSet (m229 b i) :=
  ((m101 b.c i).image (continuous_id.sub continuous_const)).isClosed.measurableSet
end AreaScope17
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope18
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 cross2)
private theorem M4.BulkBoundary.m233 (b : m69) (i : Fin 4) (z : Pt)
    (hz:z≠0) (hp:inner ℝ (m91 b i 0) z=0) : m140 b i z ≠ 0 := by
  intro he
  have h0:inner ℝ (m92 b i 0) z=0:=by
    have h:=congrArg (fun x:E2=>x 0) he
    exact h
  have h1:inner ℝ (m93 b i 0) z=0:=by
    have h:=congrArg (fun x:E2=>x 1) he
    exact h
  have h:=m182 b i z
  simp only [h0,h1,hp,zero_smul,zero_add] at h
  exact hz h.symm
private theorem M4.BulkBoundary.m234 (n u v : Pt) (ht:inner ℝ u n≠0) :
    inner ℝ n (Gnomonic.projectVelocity n u v)=0:=by
  unfold Gnomonic.projectVelocity
  have ht':inner ℝ n u ≠ 0:=by rwa [real_inner_comm]
  simp only [inner_add_right,real_inner_smul_right]
  field_simp [ht']
  simp only [real_inner_comm u n,real_inner_comm v n]
  ring
private theorem M4.BulkBoundary.m235 (b : m69) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:m94 b i j t∈patch b.c i) :
    m146 b i j =ᶠ[nhds t] m99 b i j := by
  let f:ℝ→ℝ:=fun s=>inner ℝ (m91 b i 0) (m94 b i j s-b.c i)
  have hc:Continuous f:=by
    unfold f
    exact continuous_const.inner ((m96 b i j).continuous.sub continuous_const)
  have hOpen:IsOpen {s:ℝ|m143 b i<f s}:=isOpen_lt continuous_const hc
  have ht:m143 b i<f t:=by
    have h:=m111 b i (m94 b i j t) hp
    have hd:=(m105 b i 0).1
    change dist (b.c i) (b.c (m79 b i 0))/4<f t
    dsimp [f] at *
    linarith
  have hMem:{s:ℝ|m143 b i<f s}∈nhds t:=hOpen.mem_nhds ht
  filter_upwards [hMem] with s hs
  exact m148 b i j s hs.le
private theorem M4.BulkBoundary.m236 (b : m69) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:m94 b i j t∈patch b.c i) :
    HasDerivAt (m119 b i j)
      (Gnomonic.projectVelocity (m91 b i 0) (m94 b i j t-b.c i)
        (Gnomonic.capVelocity (m92 b i j) (m93 b i j) (m142 b i j) t)) t ∧
    Gnomonic.projectVelocity (m91 b i 0) (m94 b i j t-b.c i)
        (Gnomonic.capVelocity (m92 b i j) (m93 b i j) (m142 b i j) t)≠0:=by
  let h:ℝ:=m142 b i j
  have hh:|h|<1:=by
    change |dist (b.c i) (b.c (m79 b i j))/2| < 1
    rw [abs_of_pos (half_pos (m105 b i j).1)]
    change dist (b.c i) (b.c (m79 b i j))/2<1
    linarith [(m105 b i j).2]
  have he:m119 b i j=Gnomonic.projectedArc (m91 b i 0) (m91 b i j)
      (m92 b i j) (m93 b i j) h:=by
    funext s
    unfold m119 Gnomonic.projectedArc
    exact congrArg (Gnomonic.project (m91 b i 0)) (m118 b i j s)
  have hvis:t∈Gnomonic.visible (m91 b i 0) (m91 b i j)
      (m92 b i j) (m93 b i j) h:=by
    change 0 < inner ℝ (Gnomonic.capArc (m91 b i j) (m92 b i j) (m93 b i j)
      (dist (b.c i) (b.c (m79 b i j))/2) t) (m91 b i 0)
    rw [←m118,real_inner_comm]
    exact m112 b i _ hp
  have H:=(Gnomonic.capArc_regular (m91 b i 0) (m91 b i j)
    (m92 b i j) (m93 b i j) h (m107 b i j) hh (m107 b i 0).aa).2.2 t hvis
  rw [he,m118]
  exact ⟨H.2.2.1,H.2.2.2⟩
private theorem M4.BulkBoundary.m237 (b : m69) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:m94 b i j t∈patch b.c i) :
    deriv (m146 b i j) t = m140 b i
      (Gnomonic.projectVelocity (m91 b i 0) (m94 b i j t-b.c i)
        (Gnomonic.capVelocity (m92 b i j) (m93 b i j) (m142 b i j) t)) := by
  rw [(m235 b i j t hp).deriv_eq]
  have H:=(m236 b i j t hp).1
  have hd:= (m140 b i).hasFDerivAt.comp_hasDerivAt t H
  have he:m99 b i j=fun s=> m140 b i (m119 b i j s):=by
    funext s
    exact (m141 b i (m94 b i j s)).symm
  rw [he]
  exact hd.deriv
private theorem M4.BulkBoundary.m238 (b : m69) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (hp:m94 b i j t∈patch b.c i) : deriv (m146 b i j) t≠0:=by
  rw [m237 b i j t hp]
  apply m233 b i
    (Gnomonic.projectVelocity (m91 b i 0) (m94 b i j t-b.c i)
        (Gnomonic.capVelocity (m92 b i j) (m93 b i j) (m142 b i j) t))
    (m236 b i j t hp).2
  apply m234
  rw [real_inner_comm]
  exact (m112 b i _ hp).ne'
private theorem M4.BulkBoundary.m239 (b : m69) (i : Fin 4) (j : Fin 3) (p : Pt)
    (hp:p∈patch b.c i) : m142 b i j ≤ inner ℝ (m91 b i j) (p-b.c i) := by
  have hk:=hp.2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
  have hb:=(CircleArc.ball_iff_inner (b.c i) (b.c (m79 b i j)) p hp.1).mp (hk _)
  have hd:=(m105 b i j).1
  have H:=mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
  have he:(dist (b.c i) (b.c (m79 b i j)))⁻¹ *
      (dist (b.c i) (b.c (m79 b i j))^2/2)=m142 b i j:=by
    unfold m142
    field_simp
  rw [he] at H
  rw [m91,real_inner_smul_left,real_inner_comm]
  exact H
private theorem M4.BulkBoundary.m240 (b : m69) (i : Fin 4) (j : Fin 3) (t:ℝ) :
    inner ℝ (m91 b i j) (m94 b i j t-b.c i)=m142 b i j := by
  rw [m118]
  have F:=m107 b i j
  simp only [Gnomonic.capArc,inner_add_right,real_inner_smul_right,F.aa,F.ae1,F.ae2,
    mul_one,mul_zero,zero_add,add_zero]
  rfl
private theorem M4.BulkBoundary.m241 (b : m69) (i : Fin 4) (j : Fin 3) (t:ℝ) :
    Gnomonic.capVelocity (m92 b i j) (m93 b i j) (m142 b i j) t =
      cross (m91 b i j) (m94 b i j t-b.c i) := by
  rw [m118]
  exact m160 _ _ _ _ (m107 b i j).aa (m107 b i j).ae1
private theorem M4.BulkBoundary.m242 (b : m69) (i : Fin 4) (j : Fin 3)
    (t:ℝ) (ht:m94 b i j t∈patch b.c i) (x:E2) (hx:x∈m98 b i) :
    0 ≤ cross2 (deriv (m146 b i j) t) (x-m146 b i j t) := by
  obtain ⟨p,hp,rfl⟩:=hx
  have hu:inner ℝ (m94 b i j t-b.c i) (m94 b i j t-b.c i)=1:=by
    have H:‖m94 b i j t-b.c i‖=1:=by
      simpa only [Metric.mem_sphere,dist_eq_norm] using ht.1
    rw [real_inner_self_eq_norm_sq,H];norm_num
  have hw:inner ℝ (p-b.c i) (p-b.c i)=1:=by
    have H:‖p-b.c i‖=1:=by simpa only [Metric.mem_sphere,dist_eq_norm] using hp.1
    rw [real_inner_self_eq_norm_sq,H];norm_num
  have hh:0≤ m142 b i j:=(half_pos (m105 b i j).1).le
  have H:=m156 b i (m91 b i j) (m94 b i j t-b.c i)
    (p-b.c i) (m142 b i j) hu hw hh (m240 b i j t)
    (m239 b i j p hp) (m112 b i _ ht)
    (m112 b i _ hp)
  rw [m237 b i j t ht,m241,
    m149 b i j t ht]
  simpa only [map_sub,m141,m99] using H
end AreaScope18
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope19
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SolidGeom.ClassicalInputs (E2 PositiveConvexBoundary cross2)
private theorem M4.BulkBoundary.m243 (b : m69) (i m : Fin 4) (hmi : m ≠ i) :
    ∃ j : Fin 3, m79 b i j = m := by
  have hothers : ∀ (i m : Fin 4), m ≠ i → ∃ j : Fin 3, m74 i j = m := by decide
  obtain ⟨j,hj⟩ := hothers i m hmi
  have hinv : ∀ j : Fin 3, m77 (m77 j) = j := by decide
  dsimp only [m79]
  split_ifs
  · exact ⟨m77 j,by rw [hinv,hj]⟩
  · exact ⟨j,hj⟩
private theorem M4.BulkBoundary.m244 : ∀ (j k : Fin 3),
    k = j ∨ k = j+1 ∨ k = (j+1)+1 := by decide
private theorem M4.BulkBoundary.m245 : ∀ j : Fin 3, j+1 ≠ (j+1)+1 := by decide
private theorem M4.BulkBoundary.m246 (b : m69) (i : Fin 4) (j : Fin 3) (p : Pt)
    (hpair : p ∈ Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1)
    (hK : p ∈ Kset b.c) (m : Fin 4) (hmi : m ≠ i) (hmj : m ≠ m79 b i j)
    (hsm : dist p (b.c m) = 1) :
    p = m84 b i j ∨ p = m85 b i j := by
  obtain ⟨k,hk⟩ := m243 b i m hmi
  have hkj : k ≠ j := fun h => hmj (by rw [← hk,h])
  rcases m244 j k with he | he | he
  · exact (hkj he).elim
  · have htr : p ∈ triplePts b.c (m79 b i ((j+1)+1)) := by
      intro a ha
      by_cases hai : a = i
      · subst a; exact hpair.1
      · obtain ⟨r,hr⟩ := m243 b i a hai
        rcases m244 j r with her | her | her
        · rw [← hr,her]; exact hpair.2
        · rw [← hr,her,← he,hk]; exact hsm
        · exact (ha (by rw [← hr,her])).elim
    have hmem : p ∈ triplePts b.c (m79 b i ((j+1)+1)) ∩ Kset b.c := ⟨htr,hK⟩
    rw [m72] at hmem
    exact Or.inr (Set.mem_singleton_iff.mp hmem)
  · have htr : p ∈ triplePts b.c (m79 b i (j+1)) := by
      intro a ha
      by_cases hai : a = i
      · subst a; exact hpair.1
      · obtain ⟨r,hr⟩ := m243 b i a hai
        rcases m244 j r with her | her | her
        · rw [← hr,her]; exact hpair.2
        · exact (ha (by rw [← hr,her])).elim
        · rw [← hr,her,← he,hk]; exact hsm
    have hmem : p ∈ triplePts b.c (m79 b i (j+1)) ∩ Kset b.c := ⟨htr,hK⟩
    rw [m72] at hmem
    exact Or.inl (Set.mem_singleton_iff.mp hmem)
private theorem M4.BulkBoundary.m247 (b : m69) (i : Fin 4) (j : Fin 3) :
    Set.InjOn (m94 b i j) (Set.Ico 0 (2*Real.pi)) := by
  intro x hx y hy hxy
  have hspan : max x y-min x y < 2*Real.pi := by
    have hl : 0 ≤ min x y := le_min hx.1 hy.1
    have hu : max x y < 2*Real.pi := max_lt hx.2 hy.2
    linarith
  have hi := m117 (m89 b i j) ![m92 b i j,m93 b i j]
    (m108 b i j) (m90 b i j) (m106 b i j)
    (min x y) (max x y) hspan
  exact hi ⟨min_le_left _ _,le_max_left _ _⟩ ⟨min_le_right _ _,le_max_right _ _⟩ hxy
private theorem M4.BulkBoundary.m248 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2*Real.pi)) (hK : m94 b i j t ∈ Kset b.c)
    (m : Fin 4) (hmi : m ≠ i) (hmj : m ≠ m79 b i j)
    (hsm : dist (m94 b i j t) (b.c m) = 1) :
    t = 0 ∨ t = m95 b i j := by
  have hp := m246 b i j (m94 b i j t)
    (m110 b i j t) hK m hmi hmj hsm
  have hi := m247 b i j
  rcases hp with hp | hp
  · left
    exact hi ht ⟨le_rfl,by positivity⟩ (hp.trans (m109 b i j).symm)
  · right
    exact hi ht ⟨(m115 b i j).le,m176 b i j⟩
      (hp.trans (m170 b i j).symm)
private def M4.BulkBoundary.m249 (b : m69) (i : Fin 4) (j k : Fin 3) (t : ℝ) : ℝ :=
  inner ℝ (b.c (m79 b i k)-b.c i) (m94 b i j t-b.c i)-
    ‖b.c (m79 b i k)-b.c i‖^2/2
private def M4.BulkBoundary.m250 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) : ℝ :=
  min (m249 b i j (j+1) t) (m249 b i j ((j+1)+1) t)
private theorem M4.BulkBoundary.m251 (b : m69) (i : Fin 4) (j k : Fin 3) :
    Continuous (m249 b i j k) := by
  unfold m249 m94 SphereGeom.circlePt
  fun_prop
private theorem M4.BulkBoundary.m252 (b : m69) (i : Fin 4) (j : Fin 3) :
    Continuous (m250 b i j) :=
  (m251 b i j (j+1)).min (m251 b i j ((j+1)+1))
private theorem M4.BulkBoundary.m253 (b : m69) (i : Fin 4) (j k : Fin 3) (t : ℝ) :
    0 ≤ m249 b i j k t ↔ m94 b i j t ∈ Metric.closedBall (b.c (m79 b i k)) 1 := by
  have h := CircleArc.ball_iff_inner (b.c i) (b.c (m79 b i k)) (m94 b i j t)
    (m110 b i j t).1
  have hn : ‖b.c (m79 b i k)-b.c i‖^2 = dist (b.c i) (b.c (m79 b i k))^2 := by
    rw [← dist_eq_norm,dist_comm]
  simp only [m249,sub_nonneg,hn]
  simpa only [real_inner_comm] using h.symm
private theorem M4.BulkBoundary.m254 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    0 ≤ m250 b i j t ↔ m94 b i j t ∈ Kset b.c := by
  rw [m250,le_min_iff,m253,m253]
  constructor
  · rintro ⟨hk,hl⟩
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
    intro m
    by_cases hm : m = i
    · subst m; exact (m110 b i j t).1.le
    · obtain ⟨k,hk'⟩ := m243 b i m hm
      rcases m244 j k with he | he | he
      · rw [← hk',he]; exact (m110 b i j t).2.le
      · rw [← hk',he]; exact hk
      · rw [← hk',he]; exact hl
  · intro hK
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hK
    exact ⟨hK _,hK _⟩
private theorem M4.BulkBoundary.m255 (b : m69) (i : Fin 4) (j k : Fin 3) (t : ℝ) :
    m249 b i j k t = 0 ↔ dist (m94 b i j t) (b.c (m79 b i k)) = 1 := by
  let u := m94 b i j t-b.c i
  let v := b.c (m79 b i k)-b.c i
  have hu : ‖u‖ = 1 := (m110 b i j t).1
  have hsq : dist (m94 b i j t) (b.c (m79 b i k))^2 =
      1-2*inner ℝ v u+‖v‖^2 := by
    have hv : m94 b i j t-b.c (m79 b i k) = u-v := by dsimp [u,v]; abel
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu]
    rw [real_inner_comm]
    ring
  change inner ℝ v u-‖v‖^2/2 = 0 ↔ _
  constructor <;> intro h
  · nlinarith [dist_nonneg (x:=m94 b i j t) (y:=b.c (m79 b i k))]
  · rw [h] at hsq
    nlinarith
private theorem M4.BulkBoundary.m256 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2*Real.pi)) (hz : m250 b i j t = 0) :
    t = 0 ∨ t = m95 b i j := by
  have hK := (m254 b i j t).mp hz.ge
  have hmin : m249 b i j (j+1) t = 0 ∨ m249 b i j ((j+1)+1) t = 0 := by
    rcases le_total (m249 b i j (j+1) t) (m249 b i j ((j+1)+1) t) with h | h
    · exact Or.inl (by simpa only [m250,min_eq_left h] using hz)
    · exact Or.inr (by simpa only [m250,min_eq_right h] using hz)
  rcases hmin with h | h
  · exact m248 b i j t ht hK _ (m80 b i (j+1))
      (fun he => m82 j (m81 b i he).symm)
      ((m255 b i j (j+1) t).mp h)
  · exact m248 b i j t ht hK _ (m80 b i ((j+1)+1))
      (fun he => m83 j (m81 b i he).symm)
      ((m255 b i j ((j+1)+1) t).mp h)
private theorem M4.BulkBoundary.m257 (f : ℝ → ℝ) (hf : Continuous f) (a b s : ℝ)
    (hs : s ∈ Set.Ioo a b) (hfs : 0 < f s)
    (hzero : ∀ t ∈ Set.Ioo a b, f t ≠ 0) : ∀ t ∈ Set.Ioo a b, 0 < f t := by
  intro t ht
  by_contra h
  have hft : f t < 0 := lt_of_le_of_ne (le_of_not_gt h) (hzero t ht)
  have hmid := isPreconnected_Ioo.intermediate_value ht hs hf.continuousOn
  obtain ⟨r,hr,hfr⟩ := hmid (show 0 ∈ Set.Icc (f t) (f s) from ⟨hft.le,hfs.le⟩)
  exact hzero r hr hfr
private theorem M4.BulkBoundary.m258 (f : ℝ → ℝ) (d : ℝ) (h0 : f 0 = 0)
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
private def M4.BulkBoundary.m259 (X Y s : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0,1,1,Y], ![1,0,X,1], ![1,X,0,s], ![Y,1,s,0]]
private theorem M4.BulkBoundary.m260 (b : m69) (i j : Fin 4) : q b.c i j = m259 b.X b.Y b.s i j := by
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
    | simp [q,m259]
private theorem M4.BulkBoundary.m261 (b : m69) (i a d l : Fin 4)
    (hia : i ≠ a) (hid : i ≠ d) (hil : i ≠ l)
    (had : a ≠ d) (hal : a ≠ l) (hdl : d ≠ l) :
    TripleGeometry.faceDelta (b.c a-b.c i) (b.c d-b.c i) = Dpoly b.X b.Y b.s l ∧
    TripleGeometry.faceQ (b.c a-b.c i) (b.c d-b.c i) = Qpoly b.X b.Y b.s l ∧
    4*(inner ℝ (b.c l-b.c i) (cross (b.c a-b.c i) (b.c d-b.c i)))^2 = Hpoly b.X b.Y b.s := by
  have hg := gram_from_q b.c i a d l
  simp only [real_inner_comm] at hg
  rw [hg]
  simp only [TripleGeometry.faceDelta,TripleGeometry.faceQ,TG_sq_q,TG_sq_diff_q,
    m260]
  fin_cases i <;> fin_cases a <;> fin_cases d <;> fin_cases l <;> norm_num at *
  all_goals simp [gramPoly,DeltaT,QT,Dpoly,Qpoly,Hpoly,m259]
  all_goals constructor
  all_goals try constructor
  all_goals ring
private theorem M4.BulkBoundary.m262 (v w z u : Pt) (hD : 0 < TripleGeometry.faceDelta v w)
    (hQ : 0 < TripleGeometry.faceQ v w) (hG : inner ℝ z (cross v w) ≠ 0)
    (hset : TripleGeometry.triple v w ∩ Metric.closedBall z 1 = {u}) :
    u = TripleGeometry.center v w+TripleGeometry.height v w • TripleGeometry.orientedNormal v w z := by
  let p := TripleGeometry.center v w+TripleGeometry.height v w • TripleGeometry.orientedNormal v w z
  let m := TripleGeometry.center v w-TripleGeometry.height v w • TripleGeometry.orientedNormal v w z
  have htr := TripleGeometry.triple_exact v w z hD hQ
  have hu : u ∈ TripleGeometry.triple v w ∩ Metric.closedBall z 1 := by rw [hset]; exact Set.mem_singleton _
  have ht := hu.1
  rw [htr] at ht
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
  rcases ht with ht | ht
  · exact ht
  · have hm : ‖m-z‖ ≤ 1 := by simpa only [ht,Metric.mem_closedBall,dist_eq_norm] using hu.2
    have hp := TripleGeometry.fourth_sq_formula v w z (TripleGeometry.height v w) hD hQ rfl
    have hn := TripleGeometry.fourth_sq_formula v w z (-TripleGeometry.height v w) hD hQ
      (neg_sq _)
    have hmform : ‖m-z‖^2-1 = TripleGeometry.sq z-
        2*inner ℝ z (TripleGeometry.center v w)+
        2*TripleGeometry.height v w*inner ℝ z (TripleGeometry.orientedNormal v w z) := by
      dsimp [m]
      simpa only [neg_smul,sub_eq_add_neg,neg_mul,mul_neg,sub_neg_eq_add,neg_neg] using hn
    have hpball : p ∈ Metric.closedBall z 1 := by
      have hh := TripleGeometry.height_pos v w hD hQ
      have hh' := TripleGeometry.normal_oriented v w z hD hG
      have hpn : ‖p-z‖ ≤ 1 := by
        change ‖p-z‖^2-1 = _ at hp
        nlinarith [norm_nonneg (p-z),norm_nonneg (m-z),mul_pos hh hh']
      exact hpn
    have hpt : p ∈ TripleGeometry.triple v w := by
      rw [htr]
      exact Or.inl rfl
    have hpu : p = u := by
      have hh : p ∈ ({u} : Set Pt) := by
        rw [← hset]
        exact ⟨hpt,hpball⟩
      exact Set.mem_singleton_iff.mp hh
    have hpm := TripleGeometry.triple_points_ne v w z hD hQ
    exact (hpm (hpu.trans ht)).elim
private theorem M4.BulkBoundary.m263 (b : m69) (i a d l : Fin 4)
    (hia : i ≠ a) (hid : i ≠ d) (hil : i ≠ l)
    (had : a ≠ d) (hal : a ≠ l) (hdl : d ≠ l) :
    m71 b l-b.c i = TripleGeometry.center (b.c a-b.c i) (b.c d-b.c i)+
      TripleGeometry.height (b.c a-b.c i) (b.c d-b.c i) •
        TripleGeometry.orientedNormal (b.c a-b.c i) (b.c d-b.c i) (b.c l-b.c i) := by
  have hp := m261 b i a d l hia hid hil had hal hdl
  have hD : 0 < TripleGeometry.faceDelta (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.1]; exact path_Dpoly_pos b.c b.X b.Y b.s b.path l
  have hQ : 0 < TripleGeometry.faceQ (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.2.1]; exact path_Qpoly_pos b.c b.X b.Y b.s b.path l
  have hG : inner ℝ (b.c l-b.c i) (cross (b.c a-b.c i) (b.c d-b.c i)) ≠ 0 := by
    intro hz; rw [hz] at hp; nlinarith [b.path.H_pos,hp.2.2]
  have hlabels : ∀ m : Fin 4, m = i ∨ m = a ∨ m = d ∨ m = l := by
    fin_cases i <;> fin_cases a <;> fin_cases d <;> fin_cases l <;> norm_num at *
    all_goals decide
  have hset : TripleGeometry.triple (b.c a-b.c i) (b.c d-b.c i) ∩
      Metric.closedBall (b.c l-b.c i) 1 = {m71 b l-b.c i} := by
    ext u
    have he : u+b.c i ∈ triplePts b.c l ∩ Kset b.c ↔
        u ∈ TripleGeometry.triple (b.c a-b.c i) (b.c d-b.c i) ∩
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
    rw [← he,m72]
    simp only [Set.mem_singleton_iff,eq_sub_iff_add_eq]
  exact m262 _ _ _ _ hD hQ hG hset
private lemma M4.BulkBoundary.m264 (v w z : Pt) : det3 v z w = -det3 v w z := by
  simp only [det3,TripleGeometry.inner_coords,TripleGeometry.cross_coords]
  simp
  ring
private lemma M4.BulkBoundary.m265 (v w z : Pt) : det3 w z v = det3 v w z := by
  simp only [det3,TripleGeometry.inner_coords,TripleGeometry.cross_coords]
  simp
  ring
private lemma M4.BulkBoundary.m266 (v w : Pt) (a : ℝ) : cross (a • v) w = a • cross v w := by
  ext k
  fin_cases k <;> simp [TripleGeometry.cross_coords] <;> ring
private lemma M4.BulkBoundary.m267 (v w : Pt) (a : ℝ) : cross v (a • w) = a • cross v w := by
  have hh := m157 v w (0 : Pt) a 0
  simpa only [zero_smul,add_zero] using hh
private theorem M4.BulkBoundary.m268 (b : m69) (i : Fin 4) (j : Fin 3) :
    0 < det3 (b.c (m79 b i j)-b.c i)
      (b.c (m79 b i (j+1))-b.c i) (b.c (m79 b i ((j+1)+1))-b.c i) := by
  let v := b.c (m74 i 0)-b.c i
  let w := b.c (m74 i 1)-b.c i
  let z := b.c (m74 i 2)-b.c i
  have ho : ∀ j k : Fin 3, j ≠ k → m74 i j ≠ m74 i k :=
    fun j k h => fun he => h (m76 i he)
  have hp := m261 b i (m74 i 0) (m74 i 1) (m74 i 2)
    (m75 i 0).symm (m75 i 1).symm (m75 i 2).symm
    (ho 0 1 (by decide)) (ho 0 2 (by decide)) (ho 1 2 (by decide))
  have hz : det3 v w z ≠ 0 := by
    intro he
    have hg := hp.2.2
    change 4*(inner ℝ z (cross v w))^2 = Hpoly b.X b.Y b.s at hg
    rw [real_inner_comm] at hg
    change 4*(det3 v w z)^2 = Hpoly b.X b.Y b.s at hg
    rw [he] at hg
    nlinarith [b.path.H_pos]
  have hfirst : 0 < det3 (b.c (m79 b i 0)-b.c i)
      (b.c (m79 b i 1)-b.c i) (b.c (m79 b i 2)-b.c i) := by
    unfold m79
    dsimp only
    change 0 < det3 (b.c (if det3 v w z < 0 then m74 i (m77 0) else m74 i 0)-b.c i)
      (b.c (if det3 v w z < 0 then m74 i (m77 1) else m74 i 1)-b.c i)
      (b.c (if det3 v w z < 0 then m74 i (m77 2) else m74 i 2)-b.c i)
    split_ifs with h
    · change 0 < det3 v z w
      rw [m264]
      exact neg_pos.mpr h
    · change 0 < det3 v w z
      exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hz)
  fin_cases j
  · simpa using hfirst
  · change 0 < det3 (b.c (m79 b i 1)-b.c i) (b.c (m79 b i 2)-b.c i)
      (b.c (m79 b i 0)-b.c i)
    rw [m265]; exact hfirst
  · change 0 < det3 (b.c (m79 b i 2)-b.c i) (b.c (m79 b i 0)-b.c i)
      (b.c (m79 b i 1)-b.c i)
    rw [m265,m265]; exact hfirst
private theorem M4.BulkBoundary.m269 (v w z : Pt) (hD : 0 < TripleGeometry.faceDelta v w)
    (hQ : 0 < TripleGeometry.faceQ v w) (hG : inner ℝ z (cross v w) < 0) :
    0 < inner ℝ w (cross v (TripleGeometry.center v w+
      TripleGeometry.height v w • TripleGeometry.orientedNormal v w z)) := by
  have hN : TripleGeometry.orientedNormal v w z = -(‖cross v w‖⁻¹ • cross v w) := by
    rw [TripleGeometry.orientedNormal,if_neg (not_lt_of_ge hG.le)]
  have hC : inner ℝ w (cross v (TripleGeometry.center v w)) = 0 := by
    unfold TripleGeometry.center
    rw [m157]
    simp only [inner_add_right,real_inner_smul_right,m158,
      TripleGeometry.cross_w,inner_zero_right,mul_zero,zero_add]
  have hGram : inner ℝ w (cross v (cross v w)) = -TripleGeometry.faceDelta v w/4 := by
    rw [m159,inner_sub_right,real_inner_smul_right,real_inner_smul_right]
    have hd := TripleGeometry.delta_gram v w
    change TripleGeometry.faceDelta v w = 4*(inner ℝ v v*inner ℝ w w-(inner ℝ v w)^2) at hd
    rw [real_inner_comm v w]
    nlinarith [hd]
  have hscale : inner ℝ w (cross v (TripleGeometry.orientedNormal v w z)) =
      ‖cross v w‖⁻¹*(TripleGeometry.faceDelta v w/4) := by
    rw [hN,show -(‖cross v w‖⁻¹ • cross v w) = (-‖cross v w‖⁻¹) • cross v w by rw [neg_smul],
      m267,real_inner_smul_right,hGram]
    ring
  have hh := m157 v (TripleGeometry.center v w) (TripleGeometry.orientedNormal v w z)
    1 (TripleGeometry.height v w)
  rw [one_smul] at hh
  rw [hh,inner_add_right,real_inner_smul_right,real_inner_smul_right,hC,one_mul,zero_add,hscale]
  exact mul_pos (TripleGeometry.height_pos v w hD hQ)
    (mul_pos (inv_pos.mpr (TripleGeometry.cross_norm_pos v w hD)) (div_pos hD (by norm_num)))
private theorem M4.BulkBoundary.m270 (b : m69) (i : Fin 4) (j : Fin 3) :
    0 < inner ℝ (b.c (m79 b i ((j+1)+1))-b.c i)
      (cross (m91 b i j) (m84 b i j-b.c i)) := by
  let a := m79 b i j
  let d := m79 b i ((j+1)+1)
  let l := m79 b i (j+1)
  have had : a ≠ d := fun h => m83 j (m81 b i h)
  have hal : a ≠ l := fun h => m82 j (m81 b i h)
  have hdl : d ≠ l := fun h => m245 j (m81 b i h).symm
  have hp := m261 b i a d l (m80 b i j).symm
    (m80 b i ((j+1)+1)).symm (m80 b i (j+1)).symm had hal hdl
  have hr := m263 b i a d l (m80 b i j).symm
    (m80 b i ((j+1)+1)).symm (m80 b i (j+1)).symm had hal hdl
  have hG : inner ℝ (b.c l-b.c i) (cross (b.c a-b.c i) (b.c d-b.c i)) < 0 := by
    have hg := m268 b i j
    have he := m264 (b.c a-b.c i) (b.c l-b.c i) (b.c d-b.c i)
    change det3 (b.c a-b.c i) (b.c d-b.c i) (b.c l-b.c i) = _ at he
    rw [real_inner_comm]
    change det3 (b.c a-b.c i) (b.c d-b.c i) (b.c l-b.c i) < 0
    rw [he]
    exact neg_neg_of_pos hg
  have hD : 0 < TripleGeometry.faceDelta (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.1]; exact path_Dpoly_pos b.c b.X b.Y b.s b.path l
  have hQ : 0 < TripleGeometry.faceQ (b.c a-b.c i) (b.c d-b.c i) := by
    rw [hp.2.1]; exact path_Qpoly_pos b.c b.X b.Y b.s b.path l
  change 0 < inner ℝ (b.c d-b.c i) (cross (m91 b i j) (m71 b l-b.c i))
  rw [hr,m91,m266,real_inner_smul_right]
  exact mul_pos (inv_pos.mpr (m105 b i j).1)
    (m269 _ _ _ hD hQ hG)
private theorem M4.BulkBoundary.m271 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    m94 b i j (t+2*Real.pi) = m94 b i j t := by
  simp only [m94,SphereGeom.circlePt,Real.cos_add_two_pi,Real.sin_add_two_pi]
private theorem M4.BulkBoundary.m272 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ) :
    m250 b i j (t+2*Real.pi) = m250 b i j t := by
  simp only [m250,m249,m271]
private theorem M4.BulkBoundary.m273 (b : m69) (i : Fin 4) (j : Fin 3) :
    0 < m249 b i j (j+1) 0 ∧ m249 b i j ((j+1)+1) 0 = 0 := by
  have hp : m84 b i j ∈ Kset b.c := (m73 b (m79 b i (j+1))).2
  have hk : m94 b i j 0 ∈ Kset b.c := by rwa [m109]
  have hnon : 0 ≤ m249 b i j (j+1) 0 :=
    (le_min_iff.mp ((m254 b i j 0).mpr hk)).1
  have hne : m249 b i j (j+1) 0 ≠ 0 := by
    intro hz
    have hs := (m255 b i j (j+1) 0).mp hz
    rw [m109] at hs
    exact (ne_of_lt (m202 b (m79 b i (j+1)))) hs
  have hd : dist (m84 b i j) (b.c (m79 b i ((j+1)+1))) = 1 := by
    exact (m73 b (m79 b i (j+1))).1 _
      (fun he => m245 j (m81 b i he).symm)
  exact ⟨lt_of_le_of_ne hnon hne.symm,
    (m255 b i j ((j+1)+1) 0).mpr (by rwa [m109])⟩
private theorem M4.BulkBoundary.m274 (b : m69) (i : Fin 4) (j : Fin 3) :
    m250 b i j 0 = 0 := by
  have h := m273 b i j
  rw [m250,h.2,min_eq_right h.1.le]
private theorem M4.BulkBoundary.m275 (b : m69) (i : Fin 4) (j : Fin 3) :
    m250 b i j (m95 b i j) = 0 := by
  have hk : m94 b i j (m95 b i j) ∈ Kset b.c := by
    rw [m170]
    exact (m73 b (m79 b i ((j+1)+1))).2
  have hn := le_min_iff.mp ((m254 b i j _).mpr hk)
  have hs : dist (m94 b i j (m95 b i j)) (b.c (m79 b i (j+1))) = 1 := by
    rw [m170]
    exact (m73 b (m79 b i ((j+1)+1))).1 _
      (fun he => m245 j (m81 b i he))
  have hz := (m255 b i j (j+1) _).mpr hs
  rw [m250,hz,min_eq_left hn.2]
private theorem M4.BulkBoundary.m276 (b : m69) (i : Fin 4) (j : Fin 3) :
    HasDerivAt (m250 b i j)
      (inner ℝ (b.c (m79 b i ((j+1)+1))-b.c i)
        (cross (m91 b i j) (m84 b i j-b.c i))) 0 := by
  let v := b.c (m79 b i ((j+1)+1))-b.c i
  have hfun : m249 b i j ((j+1)+1) = fun t =>
      inner ℝ v (m89 b i j-b.c i)+m90 b i j*
        (Real.cos t*inner ℝ v (m92 b i j)+Real.sin t*inner ℝ v (m93 b i j))-‖v‖^2/2 := by
    funext t
    unfold m249 m94 SphereGeom.circlePt
    change inner ℝ v (m89 b i j+m90 b i j •
      (Real.cos t • m92 b i j+Real.sin t • m93 b i j)-b.c i)-‖v‖^2/2 = _
    rw [show m89 b i j+m90 b i j •
      (Real.cos t • m92 b i j+Real.sin t • m93 b i j)-b.c i =
      (m89 b i j-b.c i)+m90 b i j •
      (Real.cos t • m92 b i j+Real.sin t • m93 b i j) by abel]
    simp only [inner_add_right,real_inner_smul_right]
  have hr : Real.sqrt (1-(dist (b.c i) (b.c (m79 b i j))/2)^2) = m90 b i j := by
    unfold m90 q
    congr 1
    ring
  have hT : cross (m91 b i j) (m84 b i j-b.c i) =
      m90 b i j • m93 b i j := by
    have ht := m160 (m91 b i j) (m92 b i j)
      (dist (b.c i) (b.c (m79 b i j))/2) 0 (m107 b i j).aa (m107 b i j).ae1
    rw [← m93,← m118,m109] at ht
    simpa only [Gnomonic.capVelocity,Real.sin_zero,Real.cos_zero,neg_zero,zero_smul,
      one_smul,zero_add,hr] using ht.symm
  have hcos := (Real.hasDerivAt_cos (0:ℝ)).mul_const (inner ℝ v (m92 b i j))
  have hsin := (Real.hasDerivAt_sin (0:ℝ)).mul_const (inner ℝ v (m93 b i j))
  have hh := ((hasDerivAt_const (0:ℝ) (inner ℝ v (m89 b i j-b.c i))).add
    ((hcos.add hsin).const_mul (m90 b i j))).sub_const (‖v‖^2/2)
  have hd : HasDerivAt (m249 b i j ((j+1)+1))
      (inner ℝ (b.c (m79 b i ((j+1)+1))-b.c i)
        (cross (m91 b i j) (m84 b i j-b.c i))) 0 := by
    rw [hfun,hT,real_inner_smul_right]
    simpa only [Pi.add_def,Pi.smul_def,Real.sin_zero,Real.cos_zero,neg_zero,
      zero_mul,one_mul,zero_add,add_zero] using hh
  have hstart := m273 b i j
  have hlt : m249 b i j ((j+1)+1) 0 < m249 b i j (j+1) 0 := by
    rw [hstart.2]; exact hstart.1
  have he : ∀ᶠ t in 𝓝 (0:ℝ), m249 b i j ((j+1)+1) t < m249 b i j (j+1) t :=
    (isOpen_lt (m251 b i j ((j+1)+1)) (m251 b i j (j+1))).mem_nhds hlt
  apply hd.congr_of_eventuallyEq
  filter_upwards [he] with t ht
  exact min_eq_right ht.le
private theorem M4.BulkBoundary.m277 (b : m69) (i : Fin 4) (j : Fin 3) :
    (∀ t ∈ Set.Ioo 0 (m95 b i j), 0 < m250 b i j t) ∧
    (∀ t ∈ Set.Ioo (m95 b i j) (2*Real.pi), m250 b i j t < 0) := by
  obtain ⟨ε,hε,hplus,hminus⟩ := m258 (m250 b i j) _
    (m274 b i j) (m276 b i j)
    (m270 b i j)
  let δ := min ε (min (m95 b i j) (2*Real.pi-m95 b i j))/2
  have hδ : 0 < δ := half_pos (lt_min hε (lt_min (m115 b i j)
    (sub_pos.mpr (m176 b i j))))
  have hδε : δ < ε := by
    have hh := min_le_left ε (min (m95 b i j) (2*Real.pi-m95 b i j))
    dsimp only [δ] at hδ ⊢
    linarith
  have hδL : δ < m95 b i j := by
    have hh := (min_le_right ε (min (m95 b i j) (2*Real.pi-m95 b i j))).trans
      (min_le_left _ _)
    dsimp only [δ] at hδ ⊢
    linarith
  have hδC : δ < 2*Real.pi-m95 b i j := by
    have hh := (min_le_right ε (min (m95 b i j) (2*Real.pi-m95 b i j))).trans
      (min_le_right _ _)
    dsimp only [δ] at hδ ⊢
    linarith
  have hp := hplus δ hδ hδε
  have hn : m250 b i j (2*Real.pi-δ) < 0 := by
    have h := hminus (-δ) (by linarith) (neg_neg_of_pos hδ)
    have he := m272 b i j (-δ)
    have he' : -δ+2*Real.pi = 2*Real.pi-δ := by ring
    rw [he'] at he
    rwa [he]
  constructor
  · apply m257 (m250 b i j) (m252 b i j)
      0 (m95 b i j) δ ⟨hδ,hδL⟩ hp
    intro t ht hz
    rcases m256 b i j t ⟨ht.1.le,ht.2.trans (m176 b i j)⟩ hz with h | h
    · linarith [ht.1]
    · linarith [ht.2]
  · have hneg := m257 (fun t => -m250 b i j t)
      (m252 b i j).neg (m95 b i j) (2*Real.pi) (2*Real.pi-δ)
      ⟨by linarith,by linarith⟩ (neg_pos.mpr hn)
      (by
        intro t ht hz
        have hzero : m250 b i j t = 0 := neg_eq_zero.mp hz
        rcases m256 b i j t ⟨((m115 b i j).trans ht.1).le,ht.2⟩ hzero with h | h
        · linarith [ht.1,(m115 b i j)]
        · linarith [ht.1])
    intro t ht
    exact neg_pos.mp (hneg t ht)
private theorem M4.BulkBoundary.m278 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2*Real.pi)) :
    m94 b i j t ∈ Kset b.c ↔ t ≤ m95 b i j := by
  rw [← m254]
  constructor
  · intro h
    by_contra hn
    have hs := (m277 b i j).2 t ⟨lt_of_not_ge hn,ht.2⟩
    exact (not_lt_of_ge h) hs
  · intro h
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0,m274]
    · rcases eq_or_lt_of_le h with hL | hL
      · rw [hL,m275]
      · exact ((m277 b i j).1 t ⟨h0,hL⟩).le
private theorem M4.BulkBoundary.m279 (b : m69) (i : Fin 4) (j : Fin 3) :
    m94 b i j '' Set.Icc 0 (m95 b i j) =
      patch b.c i ∩ Metric.sphere (b.c (m79 b i j)) 1 := by
  ext p
  constructor
  · rintro ⟨t,ht,rfl⟩
    have hp := m110 b i j t
    exact ⟨⟨hp.1,(m278 b i j t ⟨ht.1,ht.2.trans_lt (m176 b i j)⟩).mpr ht.2⟩,hp.2⟩
  · rintro ⟨⟨hsi,hK⟩,hsj⟩
    have hperp : ∀ a : Fin 2,
        inner ℝ (b.c (m79 b i j)-b.c i) (![m92 b i j,m93 b i j] a) = 0 := by
      have F := m107 b i j
      have hdz : (dist (b.c i) (b.c (m79 b i j)))⁻¹ ≠ 0 :=
        inv_ne_zero (ne_of_gt (m105 b i j).1)
      intro a
      fin_cases a
      · have he := F.ae1
        simp only [m91,real_inner_smul_left] at he
        simpa using (mul_eq_zero.mp he).resolve_left hdz
      · have he := F.ae2
        simp only [m91,real_inner_smul_left] at he
        simpa using (mul_eq_zero.mp he).resolve_left hdz
    have hchart := CircleArc.pair_sphere_chart_two (b.c i) (b.c (m79 b i j))
      ![m92 b i j,m93 b i j] (m108 b i j) hperp
      (m105 b i j).1 (m105 b i j).2
    have hmem : p ∈ Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1 := ⟨hsi,hsj⟩
    rw [hchart] at hmem
    change ∃ t ∈ Set.Icc 0 (2*Real.pi), m94 b i j t = p at hmem
    obtain ⟨t,ht,he⟩ := hmem
    rcases eq_or_lt_of_le ht.2 with hT | hT
    · refine ⟨0,⟨le_rfl,(m115 b i j).le⟩,?_⟩
      rw [hT] at he
      have hc : m94 b i j (2*Real.pi) = m94 b i j 0 := by
        simpa only [zero_add] using m271 b i j 0
      exact hc.symm.trans he
    · refine ⟨t,⟨ht.1,?_⟩,he⟩
      exact (m278 b i j t ⟨ht.1,hT⟩).mp (by rwa [he])
private theorem M4.BulkBoundary.m280 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Ioo 0 (m95 b i j)) (m : Fin 4) (hmi : m ≠ i)
    (hmj : m ≠ m79 b i j) : dist (m94 b i j t) (b.c m) < 1 := by
  have hp : m94 b i j t ∈ patch b.c i ∩ Metric.sphere (b.c (m79 b i j)) 1 := by
    rw [← m279]
    exact ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hk := hp.1.2
  simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hk
  apply lt_of_le_of_ne (hk m)
  intro he
  rcases m248 b i j t ⟨ht.1.le,ht.2.trans (m176 b i j)⟩
    hp.1.2 m hmi hmj he with h | h
  · linarith [ht.1]
  · linarith [ht.2]
private theorem M4.BulkBoundary.m281 (b : m69) (i : Fin 4) (j : Fin 3) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (m95 b i j)) : m94 b i j t ∈ patch b.c i := by
  have hp : m94 b i j t ∈ patch b.c i ∩ Metric.sphere (b.c (m79 b i j)) 1 := by
    rw [← m279]
    exact ⟨t,ht,rfl⟩
  exact hp.1
end AreaScope19
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope20
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open SphereGeom SolidGeom.CapPolar
private theorem M4.BulkBoundary.m282 (b : m69) (i : Fin 4) :
    ∃ P : Profile, BulkMatching P b.c i (m79 b i) ∧
      SphereGeom.cross (P.e 2) (P.e 0)=P.e 1 := by
  let n : Fin 3 → Pt := m91 b i
  let h : Fin 3 → ℝ := m142 b i
  have hn : ∀ j, ‖n j‖=1 := by
    intro j
    have H := (m107 b i j).aa
    rw [real_inner_self_eq_norm_sq] at H
    exact (sq_eq_one_iff).mp H |>.resolve_right (by nlinarith [norm_nonneg (n j)])
  have hh : ∀ j, 0 < h j := by
    intro j
    exact div_pos (m105 b i j).1 (by norm_num)
  have hi : ∀ j, h j < inner ℝ (n j) (m211 b i) := by
    intro j
    have hd := (m105 b i j).1
    have H := m213 b i j
    have he : ‖b.c (m79 b i j)-b.c i‖=dist (b.c i) (b.c (m79 b i j)) := by
      rw [dist_eq_norm,norm_sub_rev]
    rw [he] at H
    dsimp [n,h,m91,m142]
    rw [real_inner_smul_left,inv_mul_eq_div,lt_div_iff₀ hd]
    nlinarith [H]
  obtain ⟨P,hpole,hor,hnorm,hheight⟩ := profile_of_unit_oriented
    (m211 b i) (m212 b i) n hn h hh hi
  refine ⟨P,⟨m80 b i,m81 b i,?_,?_⟩,hor⟩
  · intro j
    rw [hnorm]
    rfl
  · intro j
    rw [hheight]
    rfl
private theorem M4.BulkBoundary.m283 (b : m69) (i : Fin 4) (j : Fin 3) :
    Orthonormal ℝ (fun k : Fin 3 => ![m91 b i j,m92 b i j,m93 b i j] k) := by
  have F := m107 b i j
  have h10 : inner ℝ (m92 b i j) (m91 b i j)=0 := (real_inner_comm _ _).trans F.ae1
  have h20 : inner ℝ (m93 b i j) (m91 b i j)=0 := (real_inner_comm _ _).trans F.ae2
  have h21 : inner ℝ (m93 b i j) (m92 b i j)=0 := (real_inner_comm _ _).trans F.e12
  apply orthonormal_iff_ite.mpr
  intro k l
  fin_cases k <;> fin_cases l
  all_goals first | exact F.aa | exact F.ae1 | exact F.ae2 | exact h10 | exact F.e11 | exact F.e12 | exact h20 | exact h21 | exact F.e22
private theorem M4.BulkBoundary.m284 (b : m69) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (m79 b i)) (j : Fin 3) (C : AlignedCap P j) :
    ∃ q : ℝ → ℝ, Differentiable ℝ q ∧ StrictMono q ∧
      (∀ t, q (t+2*Real.pi)=q t+2*Real.pi) ∧
      (∀ t, polar P.e (P.rho j (q t)) (q t)=m94 b i j t-b.c i) ∧
      (∀ t, capExitPoint (P.e 2) C.a C.b C.A (P.height j) (q t-C.δ)=
        m94 b i j t-b.c i) := by
  have hnormal : P.normal j=m91 b i j := hm.normal_eq j
  have hheight : P.height j=m142 b i j := hm.height_eq j
  have haxis : m91 b i j=capAxis (P.e 2) C.a C.A := hnormal.symm.trans C.normal_eq
  have hG : SphereGeom.cross (m91 b i j) (m92 b i j)=m93 b i j := rfl
  obtain ⟨r,hrd,hrm,hrp,hrpoint⟩ := cap_circle_polar_chart_ordered
    (P.e 2) C.a C.b (m91 b i j) (m92 b i j) (m93 b i j) C.A (P.height j)
    C.bounds.1 C.bounds.2.1 C.bounds.2.2 C.frame C.oriented haxis
    (m283 b i j) hG
  have hpoint : ∀ t, capExitPoint (P.e 2) C.a C.b C.A (P.height j) (r t)=
      m94 b i j t-b.c i := by
    intro t
    rw [hrpoint,hheight]
    change Gnomonic.capArc (m91 b i j) (m92 b i j) (m93 b i j)
      (m142 b i j) t=m94 b i j t-b.c i
    exact (m118 b i j t).symm
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
private theorem M4.BulkBoundary.m285 (b : m69) (i : Fin 4) :
    ∃ P : Profile, BulkMatching P b.c i (m79 b i) ∧
      SphereGeom.cross (P.e 2) (P.e 0)=P.e 1 ∧
      ∀ j : Fin 3, ∃ C : AlignedCap P j, ∃ q : ℝ → ℝ,
        Differentiable ℝ q ∧ StrictMono q ∧
        (∀ t, q (t+2*Real.pi)=q t+2*Real.pi) ∧
        (∀ t, polar P.e (P.rho j (q t)) (q t)=m94 b i j t-b.c i) ∧
        (∀ t, capExitPoint (P.e 2) C.a C.b C.A (P.height j) (q t-C.δ)=
          m94 b i j t-b.c i) := by
  obtain ⟨P,hm,hor⟩ := m282 b i
  refine ⟨P,hm,hor,?_⟩
  intro j
  obtain ⟨C⟩ := alignedCap_exists P hor j
  exact ⟨C,m284 b i P hm j C⟩
end AreaScope20
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
open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
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
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace
section AreaScope21
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
private theorem M4.BulkBoundary.m307 (b : m69) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (m79 b i)) (j : Fin 3) (φ : ℝ)
    (hφ : φ ∈ Set.Icc 0 (2*Real.pi)) :
    φ ∈ activeAzimuth P j ↔ ∃! t : ℝ,
      t ∈ Set.Icc 0 (m95 b i j) ∧ m94 b i j t=b.c i+exitPoint P φ := by
  constructor
  · intro ha
    have hu := exitPoint_mem P φ
    have hx : b.c i+exitPoint P φ ∈ patch b.c i ∩ Metric.sphere (b.c (m79 b i j)) 1 :=
      ⟨(matching_patch_iff hm _).mp hu,
        (matching_inner_sphere hm j _ hu.1).mp ((active_exit_proof P j φ).mp ha.2)⟩
    rw [← m279] at hx
    obtain ⟨t,ht,he⟩ := hx
    refine ⟨t,⟨ht,he⟩,?_⟩
    intro s hs
    exact m247 b i j
      ⟨hs.1.1,hs.1.2.trans_lt (m176 b i j)⟩
      ⟨ht.1,ht.2.trans_lt (m176 b i j)⟩ (hs.2.trans he.symm)
  · rintro ⟨t,⟨ht,he⟩,_⟩
    have hs : dist (b.c i+exitPoint P φ) (b.c (m79 b i j))=1 := by
      rw [← he]
      exact (m110 b i j t).2
    exact ⟨hφ,(active_exit_proof P j φ).mpr ((matching_inner_sphere hm j _ (exitPoint_mem P φ).1).mpr hs)⟩
private theorem M4.BulkBoundary.m308 (b : m69) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (m79 b i)) (j : Fin 3) (φ t : ℝ)
    (hφ : φ ∈ Set.Icc 0 (2*Real.pi)) (ht : t ∈ Set.Icc 0 (m95 b i j))
    (he : m94 b i j t=b.c i+exitPoint P φ) :
    φ ∈ tieAzimuth P ↔ t=0 ∨ t=m95 b i j := by
  have hu := exitPoint_mem P φ
  have hact : ∀ k : Fin 3, P.rho k φ=radius P φ ↔
      dist (m94 b i j t) (b.c (m79 b i k))=1 := by
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
    exact m248 b i j t
      ⟨ht.1,ht.2.trans_lt (m176 b i j)⟩
      (m281 b i j t ht).2 (m79 b i k) (m80 b i k)
      (fun h => hkj (m81 b i h)) ((hact k).mp hk)
  · intro htend
    have hj : P.rho j φ=radius P φ := (hact j).mpr (m110 b i j t).2
    rcases htend with h0 | hL
    · have hk : dist (m94 b i j t) (b.c (m79 b i ((j+1)+1)))=1 := by
        rw [h0,m109]
        exact (m73 b (m79 b i (j+1))).1 _
          (fun h => m245 j (m81 b i h).symm)
      exact ⟨hφ,j,(j+1)+1,m83 j,hj,(hact _).mpr hk⟩
    · have hk : dist (m94 b i j t) (b.c (m79 b i (j+1)))=1 := by
        rw [hL,m170]
        exact (m73 b (m79 b i ((j+1)+1))).1 _
          (fun h => m245 j (m81 b i h))
      exact ⟨hφ,j,j+1,m82 j,hj,(hact _).mpr hk⟩
private theorem M4.BulkBoundary.m309 (b : m69) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (m79 b i)) (j : Fin 3) (φ : ℝ)
    (hφ : φ ∈ Set.Icc 0 (2*Real.pi)) :
    (φ ∈ sector P j ∧ φ ∉ tieAzimuth P) ↔
      ∃ t ∈ Set.Ioo 0 (m95 b i j), m94 b i j t=b.c i+exitPoint P φ := by
  constructor
  · rintro ⟨hs,hn⟩
    have ha : φ ∈ activeAzimuth P j := ⟨hφ,by
      change P.rho j φ=P.rho (winner P φ) φ
      rw [hs.2]⟩
    obtain ⟨t,⟨ht,he⟩,_⟩ := (m307 b i P hm j φ hφ).mp ha
    have hne : ¬(t=0 ∨ t=m95 b i j) := fun h => hn
      ((m308 b i P hm j φ t hφ ht he).mpr h)
    exact ⟨t,⟨lt_of_le_of_ne ht.1 (fun h => hne (Or.inl h.symm)),
      lt_of_le_of_ne ht.2 (fun h => hne (Or.inr h))⟩,he⟩
  · rintro ⟨t,ht,he⟩
    have hn : φ ∉ tieAzimuth P := by
      intro hn
      rcases (m308 b i P hm j φ t hφ ⟨ht.1.le,ht.2.le⟩ he).mp hn with h | h
      · linarith [ht.1]
      · linarith [ht.2]
    have ha : P.rho j φ=radius P φ := (active_exit_proof P j φ).mpr
      ((matching_inner_sphere hm j _ (exitPoint_mem P φ).1).mpr (by
        rw [← he];exact (m110 b i j t).2))
    have hw : winner P φ=j := by
      by_contra hw
      exact hn ⟨hφ,j,winner P φ,fun h => hw h.symm,ha,rfl⟩
    exact ⟨⟨hφ,hw⟩,hn⟩
private theorem M4.BulkBoundary.m310 (b : m69) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (m79 b i)) (j : Fin 3) :
    (fun φ => b.c i+exitPoint P φ) '' activeAzimuth P j =
      m94 b i j '' Set.Icc 0 (m95 b i j) := by
  rw [HardSphereB5.Lean.Geometry.PathCore.Bridge.active_patch_circle_image P b.c i (m79 b i) hm j,
    m279]
end AreaScope21
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace
section AreaScope22
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
private theorem M4.BulkBoundary.m311 (b : m69) (i : Fin 4) (P : Profile)
    (hm : BulkMatching P b.c i (m79 b i)) (j : Fin 3) (q : ℝ → ℝ)
    (hqdiff : Differentiable ℝ q) (hqmono : StrictMono q)
    (hqpoint : ∀ t, polar P.e (P.rho j (q t)) (q t)=m94 b i j t-b.c i) :
    sector P j =ᵐ[volume]
      wrapWindow (2*Real.pi) (q 0) (q (m95 b i j)) := by
  have hwindow := SolidGeom.CapPolar.capPoint_window_image P j q hqdiff.continuous
    hqmono (m95 b i j) (m115 b i j)
  have hfin : (tieAzimuth P ∪ ({0,2*Real.pi} : Set ℝ)).Finite :=
    (HardSphereB5.Lean.Geometry.PathCore.Bridge.active_ties_finite b.path b.bulk P i (m79 b i) hm).union
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
    obtain ⟨t,ht,he⟩ := (m309 b i P hm j φ hs.1).mp ⟨hs,hntie⟩
    have ha : P.rho j φ=radius P φ := by
      change P.rho j φ=P.rho (winner P φ) φ
      rw [hs.2]
    have hc : polar P.e (P.rho j φ) φ=m94 b i j t-b.c i := by
      rw [ha]
      change exitPoint P φ=m94 b i j t-b.c i
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
    have hc : b.c i+polar P.e (P.rho j φ) φ=m94 b i j t := by
      rw [← he]
      abel
    have hp : polar P.e (P.rho j φ) φ ∈ caps P :=
      (matching_patch_iff hm _).mpr (hc.symm ▸ m281 b i j t ⟨ht.1.le,ht.2.le⟩)
    have hr : P.rho j φ=radius P φ := le_antisymm
      ((ray_membership P (P.rho j φ) φ
        ⟨(P.rho_range j φ).1.le,(P.rho_range j φ).2.le⟩).mp hp)
      (winner_min P φ j)
    have hext : m94 b i j t=b.c i+exitPoint P φ := by
      change m94 b i j t=b.c i+polar P.e (radius P φ) φ
      rw [← hr]
      exact hc.symm
    exact ((m309 b i P hm j φ ⟨hdom.1.le,hdom.2.le⟩).mpr
      ⟨t,ht,hext⟩).1
end AreaScope22
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace
section AreaScope23
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
private lemma M4.BulkBoundary.m312 (P : Profile) (j : Fin 3) : Continuous (momentDensity P j) := by
  unfold momentDensity tangent
  have hr := P.rho_continuous j
  fun_prop (disch := exact hr)
private lemma M4.BulkBoundary.m313 (P : Profile) (j : Fin 3) (C : AlignedCap P j) :
    Function.Periodic (momentDensity P j) (2*Real.pi) := by
  intro φ
  have hr : P.rho j (φ+2*Real.pi)=P.rho j φ := by
    rw [C.rho_eq,C.rho_eq,show φ+2*Real.pi-C.δ=(φ-C.δ)+2*Real.pi by ring]
    simp [exitRadius,exitCos,rayDenom,rayRadical,Real.cos_add_two_pi,Real.sin_add_two_pi]
  simp only [momentDensity,hr,tangent,Real.cos_add_two_pi,Real.sin_add_two_pi]
private theorem M4.BulkBoundary.m314 (b : m69) (i : Fin 4) :
    pMoment b.c i Finset.univ=
      ∑ j : Fin 3, (((1-(m142 b i j)^2)*m95 b i j/2) • m91 b i j+
        (m142 b i j/2) • SphereGeom.cross (m91 b i j)
          (m85 b i j-m84 b i j)) := by
  obtain ⟨P,hm,hor,H⟩ := m285 b i
  choose C q hqd hqm hqp hqpoint hqexit using H
  have hframe := orthonormal_iff_ite.mp P.frame
  have hp : inner ℝ (P.e 2) (P.e 2)=1 := by simpa only [if_true] using hframe 2 2
  have ha (j : Fin 3) : inner ℝ (C j).a (C j).a=1 := by
    have ht := orthonormal_iff_ite.mp (C j).frame 1 1
    simpa using ht
  have hpa (j : Fin 3) : inner ℝ (P.e 2) (C j).a=0 := by
    have ht := orthonormal_iff_ite.mp (C j).frame 0 1
    simpa using ht
  have hpb (j : Fin 3) : inner ℝ (P.e 2) (C j).b=0 := by
    have ht := orthonormal_iff_ite.mp (C j).frame 0 2
    simpa using ht
  have hglue (j : Fin 3) :
      capExitPoint (P.e 2) (C j).a (C j).b (C j).A (P.height j) (q j (m95 b i j)-(C j).δ)=
      capExitPoint (P.e 2) (C (j+1)).a (C (j+1)).b (C (j+1)).A (P.height (j+1)) (q (j+1) 0-(C (j+1)).δ) := by
    rw [hqexit j,hqexit (j+1),m171]
  have hset (j : Fin 3) := m311 b i P hm j (q j) (hqd j) (hqm j) (hqpoint j)
  have hint (j : Fin 3) : (∫φ in sector P j, momentDensity P j φ)=
      momentPrimitive (P.e 2) (C j).a (C j).b (C j).A (P.height j) (q j (m95 b i j)-(C j).δ)-
      momentPrimitive (P.e 2) (C j).a (C j).b (C j).A (P.height j) (q j 0-(C j).δ) := by
    have hw : q j (m95 b i j)<q j 0+2*Real.pi := by
      rw [←hqp j 0,zero_add]
      exact hqm j (m176 b i j)
    rw [setIntegral_congr_set (hset j),wrapWindow_integral_any _ (m312 P j)
      _ _ _ (by linarith [Real.pi_pos]) (hqm j (m115 b i j)) hw (m313 P j (C j))]
    exact aligned_moment_integral P j (C j) _ _
  have hlen (j : Fin 3) :
      momentAzimuth (C j).A (P.height j) (q j (m95 b i j)-(C j).δ)-
        momentAzimuth (C j).A (P.height j) (q j 0-(C j).δ)=m95 b i j := by
    have he : m91 b i j=capAxis (P.e 2) (C j).a (C j).A :=
      (hm.normal_eq j).symm.trans (C j).normal_eq
    apply cap_arc_azimuth_increment (P.e 2) (C j).a (C j).b (m91 b i j)
      (m92 b i j) (m93 b i j) (C j).A (P.height j) (m95 b i j)
      (fun t => q j t-(C j).δ) Set.univ (C j).bounds.1 (C j).bounds.2.1 (C j).bounds.2.2
      (m115 b i j) (C j).frame (C j).oriented he (m283 b i j) rfl
      isOpen_univ (by simp) ((hqd j).sub_const (C j).δ).differentiableOn
    intro t _
    change capExitPoint (P.e 2) (C j).a (C j).b (C j).A (P.height j) (q j t-(C j).δ)=_
    rw [hqexit j t,m118]
    have hh : P.height j=m142 b i j := hm.height_eq j
    rw [hh]
    rfl
  have hcyc := cyclic_sector_moment_boundary_sum 2 (P.e 2)
    (fun j => (C j).a) (fun j => (C j).b) (fun j => (C j).A) P.height
    (fun j => q j 0-(C j).δ) (fun j => q j (m95 b i j)-(C j).δ)
    (fun j => (C j).bounds.1) (fun j => (C j).bounds.2.1) (fun j => (C j).bounds.2.2)
    (fun j => (C j).frame) hp ha hpa hpb (fun j => (C j).oriented) hglue
  have hmom := (HardSphereB5.Lean.Geometry.PathCore.Bridge.profile_patch_measure hm).2
  rw [hmom,moment_eq_polar_sectors P]
  calc
    _ = ∑ j : Fin 3, ∫ψ in (q j 0-(C j).δ)..(q j (m95 b i j)-(C j).δ),
        ∫ρ in (0)..exitRadius (C j).A (P.height j) ψ,
          Real.sin ρ • polarRay (P.e 2) (C j).a (C j).b ψ ρ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hint j,sector_moment_primitive _ _ _ _ _ _ _
        (C j).bounds.1 (C j).bounds.2.1 (C j).bounds.2.2 (C j).frame]
    _ = _ := by
      rw [hcyc]
      apply Finset.sum_congr rfl
      intro j _
      rw [hlen j,← (C j).normal_eq,hm.normal_eq j,hqexit j,hqexit j,
        m170,m109,hm.height_eq j]
      have he : (m85 b i j-b.c i)-(m84 b i j-b.c i)=
          m85 b i j-m84 b i j := by abel
      rw [he]
      rfl
end AreaScope23
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope24
open M4
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open BulkBoundary
private def M4.m315 (v w : Pt) : ℝ :=
  (2*TripleGeometry.sq v*TripleGeometry.sq w-TripleGeometry.sq v^2-TripleGeometry.sq w^2+
    TripleGeometry.sq (v-w)*(TripleGeometry.sq v+TripleGeometry.sq w))/TripleGeometry.faceDelta v w
private lemma M4.m316 (v x y : Pt) (a b : ℝ) :
    cross v (a • x+b • y)=a • cross v x+b • cross v y := by
  ext k
  fin_cases k <;> simp [TripleGeometry.cross_coords] <;> ring
private lemma M4.m317 (v w : Pt) :
    cross (v-w) (TripleGeometry.center v w)=m315 v w • cross v w := by
  have hh (a b : ℝ) : cross (v-w) (a • v+b • w)=(a+b) • cross v w := by
    ext k
    fin_cases k <;> simp [TripleGeometry.cross_coords] <;> ring
  unfold TripleGeometry.center
  rw [hh]
  congr 1
  unfold m315
  ring
private lemma M4.m318 (v w : Pt) (hD : 0<TripleGeometry.faceDelta v w)
    (hQ : 0<TripleGeometry.faceQ v w) :
    TripleGeometry.height v w/‖cross v w‖=
      2*√(TripleGeometry.faceQ v w)/TripleGeometry.faceDelta v w := by
  have hn := TripleGeometry.cross_norm_pos v w hD
  have hd : TripleGeometry.faceDelta v w=4*‖cross v w‖^2 := by
    rw [TripleGeometry.delta_gram,←TripleGeometry.cross_sq,TripleGeometry.sq_eq_norm_sq]
  have hs : √(TripleGeometry.faceDelta v w)=2*‖cross v w‖ := by
    have hsq := Real.sq_sqrt hD.le
    nlinarith only [hd,hsq,Real.sqrt_nonneg (TripleGeometry.faceDelta v w),hn]
  unfold TripleGeometry.height
  rw [Real.sqrt_div hQ.le,hs]
  rw [hd]
  field_simp
  ring
private lemma M4.m319 (v w z : Pt) (hG : det3 v w z≠0) :
    TripleGeometry.orientedNormal v w z=
      (Real.sign (det3 v w z)/‖cross v w‖) • cross v w := by
  unfold TripleGeometry.orientedNormal
  have he : inner ℝ z (cross v w)=det3 v w z := by
    unfold det3
    exact real_inner_comm _ _
  rw [he]
  rcases lt_or_gt_of_ne hG with hg|hg
  · rw [if_neg (not_lt_of_gt hg),Real.sign_of_neg hg]
    simp [div_eq_mul_inv,neg_smul]
  · rw [if_pos hg,Real.sign_of_pos hg]
    simp [div_eq_mul_inv]
private theorem M4.m320 (v w z : Pt)
    (hD : 0<TripleGeometry.faceDelta v w) (hQ : 0<TripleGeometry.faceQ v w)
    (hG : det3 v w z≠0) :
    (Real.sign (det3 v w z)/4) • cross (v-w)
      (TripleGeometry.center v w+TripleGeometry.height v w • TripleGeometry.orientedNormal v w z)=
      (√(TripleGeometry.faceQ v w)/(2*TripleGeometry.faceDelta v w)) • cross (v-w) (cross v w)+
      (Real.sign (det3 v w z)*m315 v w/4) • cross v w := by
  rw [m319 v w z hG,smul_smul]
  have hn : TripleGeometry.height v w*(Real.sign (det3 v w z)/‖cross v w‖)=
      Real.sign (det3 v w z)*(2*√(TripleGeometry.faceQ v w)/TripleGeometry.faceDelta v w) := by
    calc _ = Real.sign (det3 v w z)*(TripleGeometry.height v w/‖cross v w‖) := by ring
         _ = _ := by rw [m318 v w hD hQ]
  rw [hn]
  have hlin := m316 (v-w) (TripleGeometry.center v w) (cross v w) 1
    (Real.sign (det3 v w z)*(2*√(TripleGeometry.faceQ v w)/TripleGeometry.faceDelta v w))
  simp only [one_smul] at hlin
  rw [hlin,m317,smul_add,smul_smul,smul_smul]
  rcases lt_or_gt_of_ne hG with hg|hg
  · rw [Real.sign_of_neg hg]
    rw [add_comm]
    congr 1 <;> congr 1 <;> ring
  · rw [Real.sign_of_pos hg]
    rw [add_comm]
    congr 1 <;> congr 1 <;> ring
private lemma M4.m321 (c : Fin 4 → Pt) (X Y s : ℝ) (hc : IsPathConfig c X Y s)
    (i l : Fin 4) (hil : i≠l) :
    let j := oth1 i l
    let k := oth2 i l
    Deltaf c i j k=Dpoly X Y s l ∧ Qf c i j k=Qpoly X Y s l ∧
      faceAPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l)=Apoly X Y s l ∧
      gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l)=Hpoly X Y s := by
  have h10 : q c 1 0=1 := (q_symm' c 1 0).trans hc.q01
  have h20 : q c 2 0=1 := (q_symm' c 2 0).trans hc.q02
  have h30 : q c 3 0=Y := (q_symm' c 3 0).trans hc.q03
  have h21 : q c 2 1=X := (q_symm' c 2 1).trans hc.q12
  have h31 : q c 3 1=1 := (q_symm' c 3 1).trans hc.q13
  have h32 : q c 3 2=s := (q_symm' c 3 2).trans hc.q23
  fin_cases i <;> fin_cases l <;> simp_all [oth1,oth2,Deltaf,Qf,QT,DeltaT,
    Dpoly,Qpoly,Apoly,Hpoly,faceAPoly,gramPoly,hc.q01,hc.q02,hc.q03,hc.q12,hc.q13,hc.q23]
  all_goals repeat' constructor
  all_goals ring
private lemma M4.m322 (c : Fin 4 → Pt) (i l : Fin 4) (hil : i≠l) :
    triplePts c l={x | x-c i ∈ TripleGeometry.triple (c (oth1 i l)-c i) (c (oth2 i l)-c i)} := by
  fin_cases i <;> fin_cases l <;> simp_all only [Fin.isValue,ne_eq,not_true_eq_false]
  all_goals ext x
  all_goals simp [oth1,oth2,triplePts,TripleGeometry.triple,dist_eq_norm,norm_sub_base,Fin.forall_fin_succ]
  all_goals tauto
private theorem M4.m323 (B : m69) (i l : Fin 4) (hil : i≠l) :
    m71 B l-B.c i=TripleGeometry.center (B.c (oth1 i l)-B.c i) (B.c (oth2 i l)-B.c i)+
      TripleGeometry.height (B.c (oth1 i l)-B.c i) (B.c (oth2 i l)-B.c i) •
      TripleGeometry.orientedNormal (B.c (oth1 i l)-B.c i) (B.c (oth2 i l)-B.c i) (B.c l-B.c i) := by
  let c := B.c
  let X := B.X
  let Y := B.Y
  let s := B.s
  have hc : IsPathConfig c X Y s := B.path
  let j := oth1 i l
  let k := oth2 i l
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
  have hF := m321 c X Y s hc i l hil
  have hDP : D=Dpoly X Y s l := by
    dsimp [D,v,w]
    simp only [TripleGeometry.faceDelta,TG_sq_q,TG_sq_diff_q]
    exact hF.1
  have hQP : Q=Qpoly X Y s l := by
    dsimp [Q,v,w]
    simp only [TripleGeometry.faceQ,TG_sq_q,TG_sq_diff_q]
    exact hF.2.1
  have hD : 0 < D := by rw [hDP]; exact path_Dpoly_pos c X Y s hc l
  have hQ : 0 < Q := by rw [hQP]; exact path_Qpoly_pos c X Y s hc l
  have hdet : 4*(inner ℝ z (cross v w))^2 = Hpoly X Y s := by
    have hg := gram_from_q c i j k l
    rw [hF.2.2.2] at hg
    simpa only [real_inner_comm] using hg
  have hG : inner ℝ z (cross v w) ≠ 0 := by intro hz; rw [hz] at hdet; nlinarith [hc.H_pos]
  have hn : 0 < inner ℝ z N := TripleGeometry.normal_oriented v w z hD hG
  have hh : 0 < h := TripleGeometry.height_pos v w hD hQ
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hh) hn
  have hpm : p ≠ m := by
    exact fun he => TripleGeometry.triple_points_ne v w z hD hQ (add_left_cancel he)
  have htr : triplePts c l = {p,m} := by
    rw [m322 c i l hil]
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
    exact hx.trans hF.2.2.1
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
  have hab : a^2<b^2 := hs.1 B.bulk
  have hu := m73 B l
  have hu4 : dist (m71 B l) (c l)≤1 := by
    have hx := hu.2
    change m71 B l ∈ body c Finset.univ at hx
    have hall : ∀ m,dist (m71 B l) (c m)≤1 := by
      simpa only [body,Set.mem_iInter,Finset.mem_univ,forall_true_left,Metric.mem_closedBall] using hx
    exact hall l
  have hh : m71 B l=p := by
    have htt := hu.1
    change m71 B l ∈ triplePts c l at htt
    rw [htr] at htt
    rcases Set.mem_insert_iff.mp htt with hpEq|hmEq
    · exact hpEq
    · have hmEq' := Set.mem_singleton_iff.mp hmEq
      have hsq : dist (m71 B l) (c l)^2≤1 := by
        nlinarith only [hu4,dist_nonneg (x:=m71 B l) (y:=c l)]
      rw [hmEq'] at hsq
      have hsum : a+b≤0 := by linarith only [hsq,hm]
      have hle : b^2≤a^2 := by nlinarith only [hsum,hb]
      exact False.elim (not_le_of_gt hab hle)
  rw [hh]
  dsimp [p,o,h,N,v,w,c,j,k]
  abel
private theorem M4.m324 (B : m69) (i l : Fin 4) (hil : i≠l) :
    let v := B.c (oth1 i l)-B.c i
    let w := B.c (oth2 i l)-B.c i
    let z := B.c l-B.c i
    (Real.sign (det3 v w z)/4) • cross (v-w) (m71 B l-B.c i)=
      (√(Qf B.c i (oth1 i l) (oth2 i l))/(2*Deltaf B.c i (oth1 i l) (oth2 i l))) • cross (v-w) (cross v w)+
      (Real.sign (det3 v w z)*Lapex B.c i (oth1 i l) (oth2 i l)/4) • cross v w := by
  let v := B.c (oth1 i l)-B.c i
  let w := B.c (oth2 i l)-B.c i
  let z := B.c l-B.c i
  have hF := m321 B.c B.X B.Y B.s B.path i l hil
  have hD : 0<TripleGeometry.faceDelta v w := by
    dsimp [v,w]
    simp only [TripleGeometry.faceDelta,TG_sq_q,TG_sq_diff_q]
    change 0<Deltaf B.c i (oth1 i l) (oth2 i l)
    rw [hF.1]
    exact path_Dpoly_pos B.c B.X B.Y B.s B.path l
  have hQ : 0<TripleGeometry.faceQ v w := by
    dsimp [v,w]
    simp only [TripleGeometry.faceQ,TG_sq_q,TG_sq_diff_q]
    change 0<Qf B.c i (oth1 i l) (oth2 i l)
    rw [hF.2.1]
    exact path_Qpoly_pos B.c B.X B.Y B.s B.path l
  have hG : det3 v w z≠0 := by
    have hg := gram_from_q B.c i (oth1 i l) (oth2 i l) l
    rw [hF.2.2.2] at hg
    intro hz
    change det3 v w z=0 at hz
    change 4*(det3 v w z)^2=Hpoly B.X B.Y B.s at hg
    rw [hz] at hg
    nlinarith only [hg,B.path.H_pos]
  rw [m323 B i l hil]
  have hh := m320 v w z hD hQ hG
  simpa only [v,w,z,m315,TripleGeometry.faceDelta,TripleGeometry.faceQ,TG_sq_q,TG_sq_diff_q,
    Deltaf,Qf,Lapex] using hh
private theorem M4.m325 (B : m69) (i l : Fin 4) (hil : i≠l) :
    let v := B.c (oth1 i l)-B.c i
    let w := B.c (oth2 i l)-B.c i
    let z := B.c l-B.c i
    m71 B l-B.c i=TripleGeometry.center v w+
      (Real.sign (det3 v w z)*(2*√(Qf B.c i (oth1 i l) (oth2 i l))/
        Deltaf B.c i (oth1 i l) (oth2 i l))) • cross v w := by
  let v := B.c (oth1 i l)-B.c i
  let w := B.c (oth2 i l)-B.c i
  let z := B.c l-B.c i
  have hF := m321 B.c B.X B.Y B.s B.path i l hil
  have hD : 0<TripleGeometry.faceDelta v w := by
    dsimp [v,w]
    simp only [TripleGeometry.faceDelta,TG_sq_q,TG_sq_diff_q]
    change 0<Deltaf B.c i (oth1 i l) (oth2 i l)
    rw [hF.1]
    exact path_Dpoly_pos B.c B.X B.Y B.s B.path l
  have hQ : 0<TripleGeometry.faceQ v w := by
    dsimp [v,w]
    simp only [TripleGeometry.faceQ,TG_sq_q,TG_sq_diff_q]
    change 0<Qf B.c i (oth1 i l) (oth2 i l)
    rw [hF.2.1]
    exact path_Qpoly_pos B.c B.X B.Y B.s B.path l
  have hG : det3 v w z≠0 := by
    have hg := gram_from_q B.c i (oth1 i l) (oth2 i l) l
    rw [hF.2.2.2] at hg
    intro hz
    change det3 v w z=0 at hz
    change 4*(det3 v w z)^2=Hpoly B.X B.Y B.s at hg
    rw [hz] at hg
    nlinarith only [hg,B.path.H_pos]
  rw [m323 B i l hil,m319 v w z hG,smul_smul]
  congr 1
  congr 1
  have hd : TripleGeometry.faceDelta v w=Deltaf B.c i (oth1 i l) (oth2 i l) := by
    dsimp [v,w]
    simp only [TripleGeometry.faceDelta,TG_sq_q,TG_sq_diff_q,Deltaf]
  have hq : TripleGeometry.faceQ v w=Qf B.c i (oth1 i l) (oth2 i l) := by
    dsimp [v,w]
    simp only [TripleGeometry.faceQ,TG_sq_q,TG_sq_diff_q,Qf]
  calc
    _ = Real.sign (det3 v w z)*(TripleGeometry.height v w/‖cross v w‖) := by ring
    _ = _ := by rw [m318 v w hD hQ,hd,hq]
end AreaScope24
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope25
open M4
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open BulkBoundary
private def M4.m326 (b : m69) (i l : Fin 4) : Pt :=
  let v:=b.c (oth1 i l)-b.c i
  let w:=b.c (oth2 i l)-b.c i
  let z:=b.c l-b.c i
  (Real.sign (det3 v w z)/4) • cross (v-w) (m71 b l-b.c i)
private lemma M4.m327 (b : m69) (i : Fin 4) :
    det3 (b.c (m74 i 0)-b.c i) (b.c (m74 i 1)-b.c i)
      (b.c (m74 i 2)-b.c i)≠0 := by
  let l := m74 i 2
  have hil : i≠l := (m75 i 2).symm
  have hp := m321 b.c b.X b.Y b.s b.path i l hil
  have hg := gram_from_q b.c i (oth1 i l) (oth2 i l) l
  rw [hp.2.2.2] at hg
  have h1 : oth1 i l=m74 i 0 := by fin_cases i <;> decide
  have h2 : oth2 i l=m74 i 1 := by fin_cases i <;> decide
  rw [h1,h2] at hg
  intro hz
  change 4*(det3 (b.c (m74 i 0)-b.c i) (b.c (m74 i 1)-b.c i)
    (b.c (m74 i 2)-b.c i))^2=Hpoly b.X b.Y b.s at hg
  rw [hz] at hg
  nlinarith only [hg,b.path.H_pos]
private lemma M4.m328 (b : m69) (i : Fin 4) :
    (∑ j : Fin 3,(1/4 : ℝ) • cross (b.c (m79 b i j)-b.c i)
      (m85 b i j-m84 b i j))=
      ∑ l : Fin 4,if l≠i then m326 b i l else 0 := by
  let D := det3 (b.c (m74 i 0)-b.c i) (b.c (m74 i 1)-b.c i)
    (b.c (m74 i 2)-b.c i)
  have hd : D≠0 := m327 b i
  have hr (l : Fin 4) (hil : l≠i) :
      det3 (b.c (oth1 i l)-b.c i) (b.c (oth2 i l)-b.c i) (b.c l-b.c i)=
        if l=m74 i 1 then -D else D := by
    fin_cases i <;> fin_cases l <;> simp_all [oth1,oth2,m74,D,det3,
      TripleGeometry.inner_coords,TripleGeometry.cross_coords]
    all_goals ring
  have hc (l : Fin 4) : (if l≠i then m326 b i l else 0)=
      if l≠i then ((if l=m74 i 1 then -Real.sign D else Real.sign D)/4) •
        cross ((b.c (oth1 i l)-b.c i)-(b.c (oth2 i l)-b.c i)) (m71 b l-b.c i) else 0 := by
    by_cases hil : l=i
    · simp [hil]
    · rw [if_pos hil,if_pos hil,m326,hr l hil]
      split_ifs <;> simp only [Real.sign_neg]
  simp_rw [hc]
  rcases lt_or_gt_of_ne hd with hs|hs
  · have hh : D<0 := hs
    simp only [Real.sign_of_neg hs]
    dsimp [D] at hh
    fin_cases i
    all_goals simp [m74] at hh
    all_goals simp [m84,m85,m79,m74,m77,
      Fin.sum_univ_succ,oth1,oth2,hh]
    all_goals ext k
    all_goals fin_cases k <;> simp [TripleGeometry.cross_coords] <;> ring_nf
  · have hh : ¬D<0 := not_lt_of_gt hs
    simp only [Real.sign_of_pos hs]
    dsimp [D] at hh
    fin_cases i
    all_goals simp [m74] at hh
    all_goals have hf := not_lt_of_ge hh
    all_goals simp [m84,m85,m79,m74,m77,
      Fin.sum_univ_succ,oth1,oth2,hf]
    all_goals ext k
    all_goals fin_cases k <;> simp [TripleGeometry.cross_coords] <;> ring_nf
private lemma M4.m329 (b : m69) (i l : Fin 4) (hil : i≠l) :
    m326 b i l=
      let j:=oth1 i l
      let k:=oth2 i l
      let v:=b.c j-b.c i
      let w:=b.c k-b.c i
      let z:=b.c l-b.c i
      let ε:=Real.sign (det3 v w z)
      let u:=faceCircRel b.c i j k+(ε*(2*√(Qf b.c i j k)/Deltaf b.c i j k)) • cross v w
      (ε/4) • cross (v-w) u := by
  have hh := m325 b i l hil
  have hc : TripleGeometry.center (b.c (oth1 i l)-b.c i) (b.c (oth2 i l)-b.c i)=
      faceCircRel b.c i (oth1 i l) (oth2 i l) := by
    simp only [TripleGeometry.center,TripleGeometry.faceDelta,TG_sq_q,TG_sq_diff_q,faceCircRel,Deltaf]
  dsimp only at hh ⊢
  unfold m326
  dsimp only
  rw [hh,hc]
private lemma M4.m330 (b : m69) (i : Fin 4) {E : Type*}
    [AddCommMonoid E] (f : Fin 4 → E) :
    (∑ j : Fin 3,f (m79 b i j))=∑ j : Fin 4,if j≠i then f j else 0 := by
  fin_cases i <;> simp [m79,m74,m77,Fin.sum_univ_succ] <;>split_ifs <;>simp only [_root_.add_assoc,_root_.add_comm,_root_.add_left_comm]
  all_goals first | exact _root_.add_left_comm _ _ _ | exact (_root_.add_left_comm _ _ _).symm | abel

end AreaScope25
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
section AreaScope26
open M4.BulkBoundary
open M4 HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
private theorem M4.BulkBoundary.m331 (b : m69) (i : Fin 4) (j : Fin 3) :
    m94 b i j '' Set.Icc 0 (m95 b i j) =
      Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1 ∩ Kset b.c := by
  rw [m279]
  ext p
  simp only [patch,Set.mem_inter_iff]
  exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,
    fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
private theorem M4.BulkBoundary.m332 (b : m69) (i : Fin 4) (j : Fin 3) :
    SphereGeom.arcMeasure
      (Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1 ∩ Kset b.c) =
      ENNReal.ofReal (m90 b i j * m95 b i j) := by
  rw [← m331]
  change SphereGeom.arcMeasure
    (SphereGeom.circlePt (m89 b i j) (m92 b i j) (m93 b i j)
      (m90 b i j) '' Set.Icc 0 (m95 b i j)) = _
  have h := SphereGeom.arcMeasure_circle_arc (m89 b i j)
    ![m92 b i j,m93 b i j] (m108 b i j)
    (m90 b i j) (m106 b i j) 0 (m95 b i j)
    (m115 b i j).le (by simpa only [sub_zero] using (m176 b i j).le)
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,sub_zero] using h
private theorem M4.BulkBoundary.m333 (b : m69) (i : Fin 4) (j : Fin 3) :
    (SphereGeom.arcMeasure
      (Metric.sphere (b.c i) 1 ∩ Metric.sphere (b.c (m79 b i j)) 1 ∩ Kset b.c)).toReal =
      m90 b i j * m95 b i j := by
  rw [m332,ENNReal.toReal_ofReal
    (mul_nonneg (m106 b i j).le (m115 b i j).le)]
private theorem M4.BulkBoundary.m334 (b : m69) (i : Fin 4) (j : Fin 3) :
    m95 b i j = ell b.c i (m79 b i j) := by
  unfold ell
  rw [m333]
  change m95 b i j = (m90 b i j*m95 b i j)/m90 b i j
  exact (mul_div_cancel_left₀ (m95 b i j) (ne_of_gt (m106 b i j))).symm
private theorem M4.BulkBoundary.m335 (b : m69) (i : Fin 4) (j : Fin 3) :
    ell b.c i (m79 b i j) = m95 b i j := (m334 b i j).symm
end AreaScope26
open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore M4 M4.BulkBoundary
theorem proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_moment_identity
    {c:Fin 4→Pt} {X Y s:ℝ} (hc:IsPathConfig c X Y s) (hP:0<P4poly X Y s) (i:Fin 4):
    pMoment c i Finset.univ=
      (1/2:ℝ) • (∑j:Fin 4,if j≠i then
        ((1-q c i j/4)/√(q c i j)*ell c i j) • (c j-c i) else 0)+
      (∑l:Fin 4,if l≠i then
        let j:=oth1 i l
        let k:=oth2 i l
        let v:=c j-c i
        let w:=c k-c i
        let z:=c l-c i
        let ε:=Real.sign (det3 v w z)
        let u:=faceCircRel c i j k+(ε*(2*√(Qf c i j k)/Deltaf c i j k)) • cross v w
        (ε/4) • cross (v-w) u
        else 0) := by
  let b : m69:=⟨c,X,Y,s,hc,hP⟩
  have hraw:=m314 b i
  have hed (j : Fin 3) : ((1-(m142 b i j)^2)*m95 b i j/2) • m91 b i j=
      (1/2:ℝ) • (((1-q c i (m79 b i j)/4)/√(q c i (m79 b i j))*ell c i (m79 b i j)) • (c (m79 b i j)-c i)) := by
    rw [m334]
    simp only [m142,m91,q,Real.sqrt_sq (dist_nonneg),smul_smul]
    change _ = _
    congr 1
    ring
  have hcross (j : Fin 3) :
      (m142 b i j/2) • SphereGeom.cross (m91 b i j) (m85 b i j-m84 b i j)=
      (1/4:ℝ) • cross (b.c (m79 b i j)-b.c i) (m85 b i j-m84 b i j) := by
    unfold m142 m91
    ext k
    fin_cases k <;> simp [SphereGeom.cross,crossProduct,PiLp.smul_apply]
    all_goals field_simp [(m105 b i j).1.ne'] <;>ring
  rw [Finset.sum_add_distrib] at hraw
  simp_rw [hed,hcross] at hraw
  rw [←Finset.smul_sum] at hraw
  rw [m330 b i (fun j : Fin 4 => ((1-q c i j/4)/√(q c i j)*ell c i j) • (c j-c i)),m328] at hraw
  have hcorm : (∑l:Fin 4,if l≠i then m326 b i l else 0)=
      (∑l:Fin 4,if l≠i then
        let j:=oth1 i l
        let k:=oth2 i l
        let v:=c j-c i
        let w:=c k-c i
        let z:=c l-c i
        let ε:=Real.sign (det3 v w z)
        let u:=faceCircRel c i j k+(ε*(2*√(Qf c i j k)/Deltaf c i j k)) • cross v w
        (ε/4) • cross (v-w) u else 0) := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l=i
    · simp [hl]
    · rw [if_pos hl,if_pos hl,m329 b i l (Ne.symm hl)]
  rw [hcorm] at hraw
  exact hraw
