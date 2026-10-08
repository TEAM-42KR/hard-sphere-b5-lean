import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_face_circumcenter_identities
import HardSphereB5Lean.Theorems.Thm_CircleArc_intervalIntersection
import HardSphereB5Lean.Theorems.Thm_CircleArc_arcIntersectionCases
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_pair_normal_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_pair_normalized_frame
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_circumradius_sq
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_pathFaceQ_pos
import HardSphereB5Lean.Theorems.Thm_CircleArc_pair_circle_on_spheres
import HardSphereB5Lean.Theorems.Thm_CircleArc_ball_iff_inner
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Aface_eq_poly
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_face_circumradius_certificate
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_triple_retention_test
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom
open scoped Classical RealInnerProductSpace Topology
set_option maxHeartbeats 1200000
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.E2.sq (x : Pt) : ℝ := ⟪x, x⟫
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.sq_eq_norm_sq (x : Pt) : sq x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.sq_nonneg (x : Pt) : 0 ≤ sq x := by rw [sq_eq_norm_sq]; positivity
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.inner_coords (x y : Pt) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1,
      v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := by
  simp [cross, SphereGeom.cross, cross_apply]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.cross_gram_identity (v w z : Pt) :
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.Dpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![DeltaT X 1 s, DeltaT 1 Y s, DeltaT 1 Y 1, DeltaT 1 1 X]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.gramPoly (a b cc d e f : ℝ) : ℝ :=
  4*a*b*d + (a+b-cc)*(a+d-e)*(b+d-f)
    - a*(b+d-f)^2 - b*(a+d-e)^2 - d*(a+b-cc)^2
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.faceAPoly (a b cc d e f : ℝ) : ℝ :=
  DeltaT a b cc * d - b*(a-b+cc)*(a+d-e) - a*(b-a+cc)*(b+d-f)
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z)^2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z)^2 -
      inner ℝ w w * (inner ℝ v z)^2 -
      inner ℝ z z * (inner ℝ v w)^2 :=
  E2.cross_gram_identity v w z
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.gram_from_q (c : Fin 4 → Pt) (i j k l : Fin 4) :
    4 * (inner ℝ (SphereGeom.cross (c j - c i) (c k - c i)) (c l - c i))^2 =
    gramPoly (q c i j) (q c i k) (q c j k) (q c i l) (q c j l) (q c k l) := by
  rw [cross_gram_identity, ← q_inner, ← q_inner, ← q_inner,
    inner_from_q, inner_from_q, inner_from_q]
  simp only [gramPoly]
  ring
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
open HardSphereB5.Lean (Pt)
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
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.near_q_symm (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.near_norm_sub_q (c : Fin 4 → Pt) (i j : Fin 4) :
    ‖c i - c j‖ ^ 2 = q c i j := by
  rw [q, dist_eq_norm]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.near_inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    2 * inner ℝ (c j - c i) (c k - c i) =
      q c i j + q c i k - q c j k := by
  have hdiff : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [← pow_two]
  rw [hdiff, near_norm_sub_q, near_norm_sub_q, near_norm_sub_q,
    near_q_symm c j i, near_q_symm c k i]
  ring
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.near_perpProj_inner (v a b : Pt) (hv : inner ℝ v v ≠ 0) :
    inner ℝ (perpProj v a) (perpProj v b) =
      inner ℝ a b - inner ℝ a v * inner ℝ b v / inner ℝ v v := by
  unfold perpProj
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right]
  rw [real_inner_comm v b]
  field_simp [hv]
  <;> ring
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_q_symm (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_radius_pos (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < Real.sqrt (1 - q c i j / 4) := by
  apply Real.sqrt_pos.2
  linarith [(p3_q_pos_lt_four hc i j hij).2]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_indices_cover (i j m : Fin 4) (hij : i ≠ j) :
    m = i ∨ m = j ∨ m = oth1 i j ∨ m = oth2 i j := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all [oth1, oth2]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_betaA_range (c : Fin 4 → Pt) (i j k : Fin 4)
    (hQ : 0 < Qf c i j k) :
    0 < betaA c i j k ∧ betaA c i j k < Real.pi := by
  apply p3_atan2_range
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hQ)
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_Qface_eq (c : Fin 4 → Pt) (i j : Fin 4) (hij : i ≠ j) :
    Qf c i j (oth1 i j) = Qface c (oth2 i j) ∧
      Qf c i j (oth2 i j) = Qface c (oth1 i j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [oth1, oth2, Qface, faceVerts, Qf, QT, DeltaT, q] <;>
    simp only [dist_comm (c 1) (c 0), dist_comm (c 2) (c 0), dist_comm (c 3) (c 0),
      dist_comm (c 2) (c 1), dist_comm (c 3) (c 1), dist_comm (c 3) (c 2)] <;> first | trivial | (constructor <;> ring) | ring
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_Q_pos (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    0 < Qf c i j (oth1 i j) ∧ 0 < Qf c i j (oth2 i j) := by
  have hQ : ∀ l, 0 < Qface c l := by
    intro l
    rw [(face_polys c X Y s hc l).1]
    exact path_Qpoly_pos c X Y s hc l
  rw [(p3_pair_Qface_eq c i j hij).1, (p3_pair_Qface_eq c i j hij).2]
  exact ⟨hQ _, hQ _⟩
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_perpProj_perp (v w : Pt) (hv : inner ℝ v v ≠ 0) :
    inner ℝ v (perpProj v w) = 0 := by
  simp only [perpProj, inner_sub_right, real_inner_smul_right]
  rw [real_inner_comm w v]
  field_simp [hv]
  <;> ring
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
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
end
section
open HardSphereB5.Lean (Pt)
private theorem CircleArc.frame_expansion (e : Fin 3 → E3) (he : Orthonormal ℝ e) (x : E3) :
    x = inner ℝ (e 0) x • e 0 + inner ℝ (e 1) x • e 1 +
      inner ℝ (e 2) x • e 2 := by
  have hspan : Submodule.span ℝ (Set.range e) = ⊤ :=
    he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])
  let B : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk he hspan.ge
  have h := B.sum_repr' x
  simpa [B, Fin.sum_univ_succ, add_assoc] using h.symm
end
section
open HardSphereB5.Lean (Pt)
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
end
section
open HardSphereB5.Lean (Pt)
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
end
section
open HardSphereB5.Lean (Pt)
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
end
section
open HardSphereB5.Lean (Pt)
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
end
section
open HardSphereB5.Lean (Pt)
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
end
section
open HardSphereB5.Lean (Pt)
private theorem CircleArc.cos_cut_periodic_shift (β θ t : ℝ) (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Real.cos β ≤ Real.cos (t - θ) ↔
      ∃ n : ℤ, t ∈ Set.Icc (θ - β + 2 * Real.pi * n) (θ + β + 2 * Real.pi * n) := by
  rw [cos_cut_periodic β (t - θ) hβ0 hβπ]
  constructor <;> rintro ⟨n, hlo, hhi⟩ <;> refine ⟨n, ?_, ?_⟩ <;> linarith
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_circle_point_int_periodic (m u v : Pt) (r t : ℝ) (n : ℤ) :
    SphereGeom.circlePt m u v r (t + 2 * Real.pi * n) =
      SphereGeom.circlePt m u v r t := by
  rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring]
  simp only [SphereGeom.circlePt, Real.cos_add_int_mul_two_pi,
    Real.sin_add_int_mul_two_pi]
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.point {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : ℝ → Pt :=
  SphereGeom.circlePt ((1/2:ℝ) • (c i+c j)) (M.e 0) (M.e 1) (Real.sqrt (1-q c i j/4))
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.arcA {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : Set Pt :=
  M.point '' Set.Icc (-betaA c i j (oth1 i j)) (betaA c i j (oth1 i j))
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.arcB {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : Set Pt :=
  M.point '' Set.Icc (phiE c i j-betaA c i j (oth2 i j)) (phiE c i j+betaA c i j (oth2 i j))
end
section
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_spheres (c : Fin 4 → Pt) (i j : Fin 4) (M : P3PairCosModel c i j) :
    Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 = M.point '' Set.Icc 0 (2*Real.pi) := by
  exact CircleArc.pair_sphere_chart_two (c i) (c j) M.e M.ortho M.perp M.dist_pos M.dist_lt_two
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_point_on_spheres (c : Fin 4 → Pt) (i j : Fin 4)
    (M : P3PairCosModel c i j) (t : ℝ) :
    M.point t ∈ Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 := by
  exact CircleArc.pair_circle_on_spheres (c i) (c j) M.e M.ortho M.perp M.dist_lt_two t
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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
end
section
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
end
section
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem HardSphereB5.Lean.Geometry.PathCore.P9_no_quadruple (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    (x : Pt) (hx : ∀ m : Fin 4, dist x (c m) = 1) : False := by
  have ha := (tetrahedron_metric hc).2.2.1
  let sx : Affine.Simplex ℝ Pt 3 := ⟨c, ha⟩
  have hspan : affineSpan ℝ (Set.range c) = ⊤ :=
    ha.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [HardSphereB5.Lean.Pt])
  obtain ⟨O, hO⟩ := circumradius_sq hc
  have hxcenter : x = sx.circumcenter := by
    apply sx.eq_circumcenter_of_dist_eq (r := 1)
    · simpa only [sx, hspan, AffineSubspace.mem_top]
    · intro m
      simpa only [dist_comm] using hx m
  have hOcenter : O = sx.circumcenter := by
    apply sx.eq_circumcenter_of_dist_eq (r := dist O (c 0))
    · simpa only [sx, hspan, AffineSubspace.mem_top]
    · intro m
      rw [dist_comm]
      exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ((hO m).trans (hO 0).symm)
  have hOx : O = x := hOcenter.trans hxcenter.symm
  have hEq := hO 0
  rw [hOx, hx 0] at hEq
  have hden : 4 * Hpoly X Y s ≠ 0 := mul_ne_zero (by norm_num) hc.H_pos.ne'
  apply hP
  have hdiv : P4poly X Y s / (4 * Hpoly X Y s) = 0 := by nlinarith [hEq]
  exact (div_eq_zero_iff).mp hdiv |>.resolve_right hden
private theorem HardSphereB5.Lean.Geometry.PathCore.P9_Qf_pos (hc : IsPathConfig c X Y s) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : 0 < Qf c i j k := by
  exact HardSphereB5.Lean.Geometry.pathFaceQ_pos c X Y s hc.q01 hc.q02 hc.q03 hc.q12 hc.q13 hc.q23
    hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one hc.H_pos i j k hij hik hjk
end
noncomputable section
open scoped Classical
section
private def CircleArc.RawPieces.intervals (a b φ : ℝ) : List (ℝ × ℝ) :=
  [(Real.pi-a, φ+b-Real.pi),
    (Real.pi+max (-a) (φ-b), Real.pi+min a (φ+b))].filter
    (fun ab => decide (ab.1 < ab.2))
private theorem CircleArc.RawPieces.bounds (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (ab : ℝ × ℝ) (hab : ab ∈ intervals a b φ) :
    0 ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ 2*Real.pi := by
  simp [intervals] at hab
  rcases hab with ⟨rfl | rfl, hlt⟩
  · dsimp at hlt ⊢
    constructor
    · linarith
    constructor
    · exact hlt
    · linarith
  · dsimp at hlt ⊢
    constructor
    · linarith [le_max_left (-a) (φ-b)]
    constructor
    · exact hlt
    · linarith [min_le_left a (φ+b)]
private theorem CircleArc.RawPieces.disjoint (a b φ : ℝ) (hbπ : b < Real.pi) :
    (intervals a b φ).Pairwise (fun ab cd => ab.2 ≤ cd.1 ∨ cd.2 ≤ ab.1) := by
  apply List.Pairwise.filter
  have hh : φ+b-Real.pi ≤ Real.pi+max (-a) (φ-b) ∨
      Real.pi+min a (φ+b) ≤ Real.pi-a := Or.inl (by linarith [le_max_right (-a) (φ-b)])
  simpa [List.pairwise_cons] using hh
private theorem CircleArc.RawPieces.cover (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hnormal : a+b ≠ φ) (hwrap : a+b+φ ≠ 2*Real.pi) (t : ℝ) :
    ((-a ≤ t-Real.pi ∧ t-Real.pi ≤ a) ∧
      ((φ-b ≤ t-Real.pi ∧ t-Real.pi ≤ φ+b) ∨
        t-Real.pi ≤ φ+b-2*Real.pi)) ↔
      ∃ ab ∈ intervals a b φ, t ∈ Set.Icc ab.1 ab.2 := by
  have hmain : max (-a) (φ-b) ≠ min a (φ+b) := by
    intro heq
    by_cases hl : -a ≤ φ-b <;> by_cases hr : a ≤ φ+b
    · rw [max_eq_right hl, min_eq_left hr] at heq
      exact hnormal (by linarith)
    · rw [max_eq_right hl, min_eq_right (le_of_not_ge hr)] at heq
      linarith
    · rw [max_eq_left (le_of_not_ge hl), min_eq_left hr] at heq
      linarith
    · rw [max_eq_left (le_of_not_ge hl), min_eq_right (le_of_not_ge hr)] at heq
      linarith
  constructor
  · rintro ⟨ht, h | h⟩
    · refine ⟨(Real.pi+max (-a) (φ-b), Real.pi+min a (φ+b)), ?_, ?_⟩
      have hle : max (-a) (φ-b) ≤ min a (φ+b) := by
        apply le_min
        · exact max_le (by linarith) (by linarith [ht.2, h.1])
        · exact max_le (by linarith) (by linarith)
      have hlt : max (-a) (φ-b) < min a (φ+b) := lt_of_le_of_ne hle hmain
      · have htpos : Real.pi+max (-a) (φ-b) < Real.pi+min a (φ+b) := by linarith
        simp [intervals, htpos]
      · constructor
        · dsimp; linarith [max_le ht.1 h.1]
        · dsimp; linarith [le_min ht.2 h.2]
    · refine ⟨(Real.pi-a, φ+b-Real.pi), ?_, ?_⟩
      have hlt : -a < φ+b-2*Real.pi := by
        apply lt_of_le_of_ne (by linarith [ht.1])
        intro heq
        exact hwrap (by linarith)
      · have htpos : Real.pi-a < φ+b-Real.pi := by linarith
        simp [intervals, htpos]
      · constructor <;> dsimp <;> linarith [ht.1]
  · rintro ⟨ab, hab, ht⟩
    simp [intervals] at hab
    rcases hab with ⟨rfl | rfl, hlt⟩
    · dsimp at ht
      refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, Or.inr ?_⟩
      linarith [ht.2]
    · dsimp at ht
      refine ⟨⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩⟩
      · linarith [ht.1, le_max_left (-a) (φ-b)]
      · linarith [ht.2, min_le_left a (φ+b)]
      · linarith [ht.1, le_max_right (-a) (φ-b)]
      · linarith [ht.2, min_le_right a (φ+b)]
end
section
open HardSphereB5.Lean (Pt)
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private structure HardSphereB5.Lean.Geometry.PathCore.P9IntervalData (f : ℝ → Pt) (S : Set Pt) where
  intervals : List (ℝ × ℝ)
  bounds : ∀ ab ∈ intervals, 0 ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ 2*Real.pi
  disjoint : intervals.Pairwise (fun ab cd => ab.2 ≤ cd.1 ∨ cd.2 ≤ ab.1)
  cover : ∀ t ∈ Set.Icc (0 : ℝ) (2*Real.pi), f t ∈ S ↔
    ∃ ab ∈ intervals, t ∈ Set.Icc ab.1 ab.2
private lemma HardSphereB5.Lean.Geometry.PathCore.P9_shifted_intervals (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) (M : P3PairCosModel c i j) :
    Nonempty (P9IntervalData (fun t => M.point (t-Real.pi)) (Kset c)) := by
  let a := betaA c i j (oth1 i j)
  let b := betaA c i j (oth2 i j)
  let φ := phiE c i j
  have ha0 : 0 < a := M.betaA_range.1
  have haπ : a < Real.pi := M.betaA_range.2
  have hb0 : 0 < b := M.betaB_range.1
  have hbπ : b < Real.pi := M.betaB_range.2
  have hφ0 : 0 < φ := M.phi_range.1
  have hφπ : φ < Real.pi := M.phi_range.2
  have hquad (u : ℝ) (hA : Real.cos u = Real.cos a)
      (hB : Real.cos (u-φ) = Real.cos b) : False := by
    have hpair := p3_model_point_on_spheres c i j M u
    have hsa := (M.sphereA u).mpr hA
    have hsb := (M.sphereB u).mpr hB
    apply P9_no_quadruple hc hP (M.point u)
    intro m
    rcases p3_indices_cover i j m hij with rfl | rfl | rfl | rfl
    · exact Metric.mem_sphere.mp hpair.1
    · exact Metric.mem_sphere.mp hpair.2
    · exact Metric.mem_sphere.mp hsa
    · exact Metric.mem_sphere.mp hsb
  have hnormal : a+b ≠ φ := by
    intro heq
    apply hquad a rfl
    have hsub : a-φ = -b := by linarith
    rw [hsub, Real.cos_neg]
  have hwrap : a+b+φ ≠ 2*Real.pi := by
    intro heq
    apply hquad (-a) (Real.cos_neg a)
    have hsub : -a-φ = b-2*Real.pi := by linarith
    rw [hsub, Real.cos_sub_two_pi]
  have hfirst (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2*Real.pi)) :
      Real.cos a ≤ Real.cos (t-Real.pi) ↔
      t-Real.pi ∈ Set.Icc (-a) a := by
    have habs : |t-Real.pi| ≤ Real.pi := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    constructor
    · intro hcos
      have hu : |t-Real.pi| ≤ a := by
        by_contra h
        have hc' := Real.cos_lt_cos_of_nonneg_of_le_pi ha0.le habs (lt_of_not_ge h)
        rw [Real.cos_abs] at hc'
        exact (not_lt_of_ge hcos) hc'
      exact abs_le.mp hu
    · intro hu
      have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (t-Real.pi)) haπ.le (abs_le.mpr hu)
      simpa only [Real.cos_abs] using hh
  have hpull (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2*Real.pi)) :
      M.point (t-Real.pi) ∈ Kset c ↔
      ((-a ≤ t-Real.pi ∧ t-Real.pi ≤ a) ∧
        ((φ-b ≤ t-Real.pi ∧ t-Real.pi ≤ φ+b) ∨
          t-Real.pi ≤ φ+b-2*Real.pi)) := by
    have hpair := p3_model_point_on_spheres c i j M (t-Real.pi)
    have hlocus := congrArg (fun S : Set Pt => M.point (t-Real.pi) ∈ S)
      (p3_pair_locus_eq c i j hij)
    simp only [Set.mem_inter_iff, hpair.1, hpair.2, true_and] at hlocus
    have hcutA : M.point (t-Real.pi) ∈ Metric.closedBall (c (oth1 i j)) 1 ↔
        t-Real.pi ∈ Set.Icc (-a) a := (M.ballA (t-Real.pi)).trans (hfirst t ht)
    rw [hlocus, hcutA]
    constructor
    · rintro ⟨hu, hball⟩
      have hmem : M.point (t-Real.pi) ∈ M.arcB := by
        rw [← p3_model_ballB_set c i j M]
        exact ⟨hpair, hball⟩
      exact ⟨hu, (CircleArc.periodicMembership
        ((1/2:ℝ) • (c i+c j)) M.e M.ortho (Real.sqrt (1-q c i j/4))
        (p3_pair_radius_pos hc i j hij) a b φ ha0 haπ hb0 hbπ hφ0 hφπ
        (t-Real.pi) hu).mp hmem⟩
    · rintro ⟨hu, hb⟩
      have hmem : M.point (t-Real.pi) ∈ M.arcB :=
        (CircleArc.periodicMembership
          ((1/2:ℝ) • (c i+c j)) M.e M.ortho (Real.sqrt (1-q c i j/4))
          (p3_pair_radius_pos hc i j hij) a b φ ha0 haπ hb0 hbπ hφ0 hφπ
          (t-Real.pi) hu).mpr hb
      rw [← p3_model_ballB_set c i j M] at hmem
      exact ⟨hu, hmem.2⟩
  refine ⟨⟨CircleArc.RawPieces.intervals a b φ,
    CircleArc.RawPieces.bounds a b φ ha0 haπ hb0 hbπ hφ0 hφπ,
    CircleArc.RawPieces.disjoint a b φ hbπ, ?_⟩⟩
  intro t ht
  exact (hpull t ht).trans (CircleArc.RawPieces.cover a b φ ha0 haπ hb0 hbπ hφ0 hφπ
    hnormal hwrap t)
private noncomputable def HardSphereB5.Lean.Geometry.PathCore.P9IntervalData.reflect {f : ℝ → Pt} {S : Set Pt}
    (D : P9IntervalData f S) : P9IntervalData (fun t => f (2*Real.pi-t)) S where
  intervals := D.intervals.map (fun ab => (2*Real.pi-ab.2, 2*Real.pi-ab.1))
  bounds := by
    intro ab hab
    obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hab
    have h := D.bounds cd hcd
    dsimp
    constructor
    · linarith [h.2.2]
    constructor
    · linarith [h.2.1]
    · linarith [h.1]
  disjoint := by
    refine List.Pairwise.map (fun ab : ℝ × ℝ => (2*Real.pi-ab.2, 2*Real.pi-ab.1))
      (fun ab cd h => ?_) D.disjoint
    dsimp
    rcases h with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  cover := by
    intro t ht
    have ht' : 2*Real.pi-t ∈ Set.Icc (0 : ℝ) (2*Real.pi) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [D.cover _ ht']
    constructor
    · rintro ⟨ab, hab, ht⟩
      refine ⟨(2*Real.pi-ab.2, 2*Real.pi-ab.1), List.mem_map.mpr ⟨ab, hab, rfl⟩, ?_⟩
      constructor <;> dsimp <;> linarith [ht.1, ht.2]
    · rintro ⟨ab, hab, ht⟩
      obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hab
      exact ⟨cd, hcd, ⟨by dsimp at ht; linarith [ht.2], by dsimp at ht; linarith [ht.1]⟩⟩
private lemma HardSphereB5.Lean.Geometry.PathCore.P9_cross_sq (v w : Pt) :
    inner ℝ (cross v w) (cross v w) =
      inner ℝ v v * inner ℝ w w - (inner ℝ v w)^2 := by
  simp only [E2.inner_coords, E2.cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.P9_cross_orientation (n : Pt) (e : Fin 2 → Pt) (he : Orthonormal ℝ e)
    (hn : ‖n‖ = 1) (hp : ∀ k, inner ℝ n (e k) = 0) :
    cross n (e 0) = e 1 ∨ cross n (e 0) = -(e 1) := by
  let v := cross n (e 0)
  have hn' : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have he00 : inner ℝ (e 0) (e 0) = 1 := by simpa using (orthonormal_iff_ite.mp he) 0 0
  have he11 : inner ℝ (e 1) (e 1) = 1 := by simpa using (orthonormal_iff_ite.mp he) 1 1
  have he01 : inner ℝ (e 0) (e 1) = 0 := by simpa using (orthonormal_iff_ite.mp he) 0 1
  have hv : inner ℝ v v = 1 := by
    simpa only [v, hn', he00, hp 0, pow_two, zero_mul, one_mul, sub_zero] using P9_cross_sq n (e 0)
  have hα : (inner ℝ v (e 1))^2 = 1 := by
    have hh := cross_gram_identity n (e 0) (e 1)
    simpa only [v, cross, hn', he00, he11, he01, hp 0, hp 1, mul_one, one_mul,
      pow_two, mul_zero, zero_mul, add_zero, sub_zero] using hh
  have hfactor : (inner ℝ v (e 1)-1)*(inner ℝ v (e 1)+1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    have hval : inner ℝ v (e 1) = 1 := by linarith
    have hcomm : inner ℝ (e 1) v = inner ℝ v (e 1) := real_inner_comm _ _
    have hnorm : ‖v-e 1‖^2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, hv, he11, hcomm, hval]
      norm_num
    have hz : v-e 1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v-e 1)])
    exact sub_eq_zero.mp hz
  · right
    have hval : inner ℝ v (e 1) = -1 := by linarith
    have hcomm : inner ℝ (e 1) v = inner ℝ v (e 1) := real_inner_comm _ _
    have hnorm : ‖v+e 1‖^2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, hv, he11, hcomm, hval]
      norm_num
    have hz : v+e 1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v+e 1)])
    exact eq_neg_iff_add_eq_zero.mpr hz
private lemma HardSphereB5.Lean.Geometry.PathCore.P9_pair_arc_exists (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) : Nonempty (PairArcDecomposition c i j) := by
  obtain ⟨M⟩ := p3_exists_cos_model hc i j hij
  obtain ⟨D⟩ := P9_shifted_intervals hc hP i j hij M
  let n := (1 / dist (c i) (c j)) • (c j-c i)
  have hn : ‖n‖ = 1 := by
    dsimp [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr M.dist_pos),
      ← dist_eq_norm]
    rw [dist_comm (c j) (c i)]
    exact one_div_mul_cancel M.dist_pos.ne'
  have hp : ∀ k, inner ℝ n (M.e k) = 0 := by
    intro k
    simp only [n, real_inner_smul_left, M.perp k, mul_zero]
  have hnorm : ‖-(M.e 0)‖ = 1 := by simp [M.ortho.1 0]
  have hperp : inner ℝ (-(M.e 0)) (c j-c i) = 0 := by
    rw [inner_neg_left, real_inner_comm]
    simp [M.perp 0]
  have hneg : cross n (-(M.e 0)) = -(cross n (M.e 0)) := by
    ext k
    fin_cases k <;> simp [cross, SphereGeom.cross, cross_apply] <;> ring
  rcases P9_cross_orientation n M.e M.ortho hn hp with h | h
  · have hchart (t : ℝ) :
        (1/2:ℝ) • (c i+c j) + Real.sqrt (1-q c i j/4) •
          (Real.cos t • (-(M.e 0)) + Real.sin t • cross n (-(M.e 0))) =
        M.point (t-Real.pi) := by
      rw [hneg, h]
      simp [P3PairCosModel.point, SphereGeom.circlePt, Real.cos_sub, Real.sin_sub,
        Real.cos_pi, Real.sin_pi]
    refine ⟨⟨-(M.e 0), hnorm, hperp, D.intervals, D.bounds, D.disjoint, ?_⟩⟩
    intro t ht
    change ((1/2:ℝ) • (c i+c j) + Real.sqrt (1-q c i j/4) •
      (Real.cos t • (-(M.e 0)) + Real.sin t • cross n (-(M.e 0)))) ∈ Kset c ↔ _
    rw [hchart]
    exact D.cover t ht
  · let E := D.reflect
    have hchart (t : ℝ) :
        (1/2:ℝ) • (c i+c j) + Real.sqrt (1-q c i j/4) •
          (Real.cos t • (-(M.e 0)) + Real.sin t • cross n (-(M.e 0))) =
        M.point (2*Real.pi-t-Real.pi) := by
      rw [hneg, h]
      have hangle : 2*Real.pi-t-Real.pi = Real.pi-t := by ring
      rw [hangle]
      simp [P3PairCosModel.point, SphereGeom.circlePt, Real.cos_sub, Real.sin_sub,
        Real.cos_pi, Real.sin_pi]
    refine ⟨⟨-(M.e 0), hnorm, hperp, E.intervals, E.bounds, E.disjoint, ?_⟩⟩
    intro t ht
    change ((1/2:ℝ) • (c i+c j) + Real.sqrt (1-q c i j/4) •
      (Real.cos t • (-(M.e 0)) + Real.sin t • cross n (-(M.e 0)))) ∈ Kset c ↔ _
    rw [hchart]
    exact E.cover t ht
end
noncomputable section
open scoped Classical
section
private def CircleArc.RawPieces.endpointSum {G : Type*} [AddCommGroup G] (F : ℝ → G) (L : List (ℝ × ℝ)) : G :=
  (L.map (fun ab => F ab.2 - F ab.1)).sum
private theorem CircleArc.RawPieces.endpointSum_two {G : Type*} [AddCommGroup G] (F : ℝ → G) (a b φ : ℝ) :
    endpointSum F (intervals a b φ) =
      (if Real.pi-a < φ+b-Real.pi then F (φ+b-Real.pi)-F (Real.pi-a) else 0) +
      (if max (-a) (φ-b) < min a (φ+b)
        then F (Real.pi+min a (φ+b))-F (Real.pi+max (-a) (φ-b)) else 0) := by
  classical
  by_cases hw : Real.pi-a < φ+b-Real.pi <;>
    by_cases hm : max (-a) (φ-b) < min a (φ+b) <;>
    simp [endpointSum, intervals, hw, hm]
private theorem CircleArc.RawPieces.canonical_endpointSum_strict {G : Type*} [AddCommGroup G]
    (F : ℝ → G) (hF : Function.Periodic F (2*Real.pi))
    (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hleft : -a ≠ φ-b) (hright : a ≠ φ+b) :
    endpointSum F (intervals a b φ) =
      (if φ-b < a ∧ a < φ+b then F (Real.pi+a) else 0) -
      (if φ-b < -a ∨ 2*Real.pi < a+b+φ then F (Real.pi-a) else 0) +
      (if φ+b < a ∨ 2*Real.pi < a+b+φ then F (Real.pi+φ+b) else 0) -
      (if -a < φ-b ∧ φ-b < a then F (Real.pi+φ-b) else 0) := by
  classical
  have hwrapF : F (φ+b-Real.pi) = F (Real.pi+φ+b) := by
    have h := hF (φ+b-Real.pi)
    have he : φ+b-Real.pi+2*Real.pi = Real.pi+φ+b := by ring
    rw [he] at h
    exact h.symm
  rw [endpointSum_two, hwrapF]
  by_cases hL : -a < φ-b
  ·
    by_cases hR : a < φ+b
    ·
      by_cases hI : φ-b < a
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : ¬ max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_neg hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : ¬ max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_neg hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
    ·
      by_cases hI : φ-b < a
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = φ-b := max_eq_right hL.le
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : ¬ φ-b < -a := by linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
  ·
    by_cases hR : a < φ+b
    ·
      by_cases hI : φ-b < a
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = a := min_eq_left hR.le
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : ¬ φ+b < a := by linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
    ·
      by_cases hI : φ-b < a
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
      ·
        by_cases hW : 2*Real.pi < a+b+φ
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_pos hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
        ·
          first
            | (exfalso; linarith)
            |
              have hmax : max (-a) (φ-b) = -a := max_eq_left (le_of_not_gt hL)
              have hmin : min a (φ+b) = φ+b := min_eq_right (le_of_not_gt hR)
              have hAm : φ-b < -a := by rcases lt_or_gt_of_ne hleft with h | h <;> linarith
              have hBp : φ+b < a := by rcases lt_or_gt_of_ne hright with h | h <;> linarith
              have hfw : ¬ Real.pi-a < φ+b-Real.pi := by linarith
              have hfm : max (-a) (φ-b) < min a (φ+b) := by rw [hmax, hmin]; linarith
              rw [if_neg hfw, if_pos hfm]
              simp only [hfw, hfm, if_pos, if_neg, hmax, hmin, hL, hR, hI, hW, hAm, hBp,
              and_self, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or,
              ite_true, ite_false, add_sub_assoc, ← sub_eq_add_neg]
              <;> abel
end
section
private def CircleArc.RawPieces.firstCap (a u : ℝ) : Prop := -a ≤ u ∧ u ≤ a
private def CircleArc.RawPieces.secondCap (b φ u : ℝ) : Prop :=
  (φ-b ≤ u ∧ u ≤ φ+b) ∨ (φ-b-2*Real.pi ≤ u ∧ u ≤ φ+b-2*Real.pi)
private theorem CircleArc.RawPieces.canonical_endpointSum {G : Type*} [AddCommGroup G]
    (F : ℝ → G) (hF : Function.Periodic F (2*Real.pi))
    (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hnormal : a+b ≠ φ) (hwrap : a+b+φ ≠ 2*Real.pi)
    (hleft : -a ≠ φ-b) (hright : a ≠ φ+b) :
    endpointSum F (intervals a b φ) =
      (if secondCap b φ a then F (Real.pi+a) else 0) -
      (if secondCap b φ (-a) then F (Real.pi-a) else 0) +
      (if firstCap a (φ+b) ∨ firstCap a (φ+b-2*Real.pi)
        then F (Real.pi+φ+b) else 0) -
      (if firstCap a (φ-b) then F (Real.pi+φ-b) else 0) := by
  classical
  have hn : φ-b ≠ a := by intro h; apply hnormal; linarith
  have hw : 2*Real.pi ≠ a+b+φ := hwrap.symm
  have hAp : secondCap b φ a ↔ φ-b < a ∧ a < φ+b := by
    unfold secondCap
    constructor
    · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
      · exact ⟨lt_of_le_of_ne hl hn, lt_of_le_of_ne hr hright⟩
      · exfalso; linarith
    · rintro ⟨hl, hr⟩
      exact Or.inl ⟨hl.le, hr.le⟩
  have hAm : secondCap b φ (-a) ↔ φ-b < -a ∨ 2*Real.pi < a+b+φ := by
    unfold secondCap
    constructor
    · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
      · exact Or.inl (lt_of_le_of_ne hl hleft.symm)
      · right
        exact lt_of_le_of_ne (by linarith) hw
    · rintro (h | h)
      · exact Or.inl ⟨h.le, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
  have hBp : firstCap a (φ+b) ∨ firstCap a (φ+b-2*Real.pi) ↔
      φ+b < a ∨ 2*Real.pi < a+b+φ := by
    unfold firstCap
    constructor
    · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
      · exact Or.inl (lt_of_le_of_ne hr hright.symm)
      · right
        exact lt_of_le_of_ne (by linarith) hw
    · rintro (h | h)
      · exact Or.inl ⟨by linarith, h.le⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
  have hBm : firstCap a (φ-b) ↔ -a < φ-b ∧ φ-b < a := by
    unfold firstCap
    constructor
    · rintro ⟨hl, hr⟩
      exact ⟨lt_of_le_of_ne hl hleft, lt_of_le_of_ne hr hn⟩
    · rintro ⟨hl, hr⟩
      exact ⟨hl.le, hr.le⟩
  simp only [hAp, hAm, hBp, hBm]
  exact canonical_endpointSum_strict F hF a b φ ha0 haπ hb0 hbπ hφ0 hφπ hleft hright
end
section
private def CircleArc.RawPieces.periodicCap (center halfAngle t : ℝ) : Prop :=
  ∃ n : ℤ, center-halfAngle+2*Real.pi*n ≤ t ∧
    t ≤ center+halfAngle+2*Real.pi*n
private theorem CircleArc.RawPieces.secondCap_periodic_iff (b φ u : ℝ) (hb0 : 0 < b) (hbπ : b < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) (hu0 : -Real.pi < u) (huπ : u < Real.pi) :
    periodicCap φ b u ↔ secondCap b φ u := by
  constructor
  · rintro ⟨n, hlo, hhi⟩
    have hn0 : n < 1 := by
      by_contra h
      have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_not_gt h)
      have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*Real.pi by positivity)
      linarith
    have hn1 : -2 < n := by
      by_contra h
      have hn : (n : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast (le_of_not_gt h)
      have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*Real.pi by positivity)
      linarith
    have hn : n = 0 ∨ n = -1 := by omega
    unfold secondCap
    rcases hn with rfl | rfl
    · left
      norm_num at hlo hhi
      exact ⟨by linarith, by linarith⟩
    · right
      norm_num at hlo hhi
      exact ⟨by linarith, by linarith⟩
  · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
    · exact ⟨0, by norm_num; exact ⟨by linarith, by linarith⟩⟩
    · exact ⟨-1, by norm_num; constructor <;> linarith⟩
private theorem CircleArc.RawPieces.firstCap_periodic_iff (a u : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hu0 : -Real.pi < u) (hu2π : u < 2*Real.pi) :
    periodicCap 0 a u ↔ firstCap a u ∨ firstCap a (u-2*Real.pi) := by
  constructor
  · rintro ⟨n, hlo, hhi⟩
    have hn0 : n < 2 := by
      by_contra h
      have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_not_gt h)
      have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*Real.pi by positivity)
      linarith
    have hn1 : -1 < n := by
      by_contra h
      have hn : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast (le_of_not_gt h)
      have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*Real.pi by positivity)
      linarith
    have hn : n = 0 ∨ n = 1 := by omega
    unfold firstCap
    rcases hn with rfl | rfl
    · left
      norm_num at hlo hhi
      exact ⟨by linarith, by linarith⟩
    · right
      norm_num at hlo hhi
      exact ⟨by linarith, by linarith⟩
  · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
    · exact ⟨0, by norm_num; exact ⟨by linarith, by linarith⟩⟩
    · exact ⟨1, by norm_num; constructor <;> linarith⟩
private theorem CircleArc.RawPieces.canonical_endpointSum_periodic {G : Type*} [AddCommGroup G]
    (F : ℝ → G) (hF : Function.Periodic F (2*Real.pi))
    (a b φ : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi)
    (hb0 : 0 < b) (hbπ : b < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi)
    (hnormal : a+b ≠ φ) (hwrap : a+b+φ ≠ 2*Real.pi)
    (hleft : -a ≠ φ-b) (hright : a ≠ φ+b) :
    endpointSum F (intervals a b φ) =
      (if periodicCap φ b a then F (Real.pi+a) else 0) -
      (if periodicCap φ b (-a) then F (Real.pi-a) else 0) +
      (if periodicCap 0 a (φ+b) then F (Real.pi+φ+b) else 0) -
      (if periodicCap 0 a (φ-b) then F (Real.pi+φ-b) else 0) := by
  classical
  have hAp := secondCap_periodic_iff b φ a hb0 hbπ hφ0 hφπ (by linarith) haπ
  have hAm := secondCap_periodic_iff b φ (-a) hb0 hbπ hφ0 hφπ (by linarith) (by linarith)
  have hBp := firstCap_periodic_iff a (φ+b) ha0 haπ (by linarith) (by linarith)
  have hBm' := firstCap_periodic_iff a (φ-b) ha0 haπ (by linarith) (by linarith)
  have hnwrap : ¬ firstCap a (φ-b-2*Real.pi) := by
    rintro ⟨hlo, hhi⟩
    linarith
  have hBm : periodicCap 0 a (φ-b) ↔ firstCap a (φ-b) := by
    simpa only [hnwrap, or_false] using hBm'
  simp only [hAp, hAm, hBp, hBm]
  exact canonical_endpointSum F hF a b φ ha0 haπ hb0 hbπ hφ0 hφπ hnormal hwrap hleft hright
end
noncomputable section
open Set MeasureTheory
section
private def EndpointIntervals.halfCover (L : List (ℝ × ℝ)) : Set ℝ :=
  {t | ∃ ab ∈ L, t ∈ Ioc ab.1 ab.2}
private def EndpointIntervals.closedCover (L : List (ℝ × ℝ)) : Set ℝ :=
  {t | ∃ ab ∈ L, t ∈ Icc ab.1 ab.2}
private def EndpointIntervals.endpointSum (F : ℝ → ℝ) (L : List (ℝ × ℝ)) : ℝ :=
  (L.map (fun ab => F ab.2 - F ab.1)).sum
@[simp] private theorem EndpointIntervals.halfCover_nil : halfCover [] = ∅ := by ext x; simp [halfCover]
@[simp] private theorem EndpointIntervals.closedCover_nil : closedCover [] = ∅ := by ext x; simp [closedCover]
@[simp] private theorem EndpointIntervals.halfCover_cons (ab : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    halfCover (ab :: L) = Ioc ab.1 ab.2 ∪ halfCover L := by
  ext x
  simp [halfCover, or_and_right, exists_or]
@[simp] private theorem EndpointIntervals.closedCover_cons (ab : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    closedCover (ab :: L) = Icc ab.1 ab.2 ∪ closedCover L := by
  ext x
  simp [closedCover, or_and_right, exists_or]
private theorem EndpointIntervals.halfCover_measurable (L : List (ℝ × ℝ)) : MeasurableSet (halfCover L) := by
  induction L with
  | nil => simp
  | cons ab L ih => simpa only [halfCover_cons] using measurableSet_Ioc.union ih
private theorem EndpointIntervals.integrableOn_halfCover (G : ℝ → ℝ) (hG : Continuous G) (L : List (ℝ × ℝ)) :
    IntegrableOn G (halfCover L) := by
  induction L with
  | nil => simp
  | cons ab L ih =>
    rw [halfCover_cons]
    exact ((hG.integrableOn_Icc).mono_set Ioc_subset_Icc_self).union ih
private theorem EndpointIntervals.halfCover_ae_closedCover (L : List (ℝ × ℝ)) :
    halfCover L =ᵐ[(volume : Measure ℝ)] closedCover L := by
  induction L with
  | nil => simp
  | cons ab L ih =>
    rw [halfCover_cons, closedCover_cons]
    exact (Ioc_ae_eq_Icc (a := ab.1) (b := ab.2)).union ih
private theorem EndpointIntervals.endpointSum_eq_integral (F G : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t) (hG : Continuous G)
    (L : List (ℝ × ℝ))
    (hb : ∀ ab ∈ L, ab.1 ≤ ab.2)
    (hd : L.Pairwise (fun ab cd => ab.2 ≤ cd.1 ∨ cd.2 ≤ ab.1)) :
    endpointSum F L = ∫ t in closedCover L, G t := by
  have hhalf : endpointSum F L = ∫ t in halfCover L, G t := by
    induction L with
    | nil => simp [endpointSum]
    | cons ab L ih =>
      have hab : ab.1 ≤ ab.2 := hb ab (by simp)
      have hbL : ∀ cd ∈ L, cd.1 ≤ cd.2 := fun cd hcd => hb cd (by simp [hcd])
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hd
      have hdisj : Disjoint (Ioc ab.1 ab.2) (halfCover L) := by
        apply Set.disjoint_left.mpr
        intro t ht hu
        obtain ⟨cd, hcd, htc⟩ := hu
        rcases hhead cd hcd with hle | hle
        · exact (not_lt_of_ge (ht.2.trans hle)) htc.1
        · exact (not_lt_of_ge (htc.2.trans hle)) ht.1
      have hFTC : (∫ t in Ioc ab.1 ab.2, G t) = F ab.2 - F ab.1 := by
        rw [← intervalIntegral.integral_of_le hab]
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
          (hG.intervalIntegrable ab.1 ab.2)
      rw [endpointSum, List.map_cons, List.sum_cons, halfCover_cons,
        setIntegral_union hdisj (halfCover_measurable L)
          ((hG.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
          (integrableOn_halfCover G hG L), hFTC]
      exact congrArg (fun x => F ab.2 - F ab.1 + x) (ih hbL htail)
  exact hhalf.trans (setIntegral_congr_set (halfCover_ae_closedCover L))
private theorem EndpointIntervals.endpointSum_eq_of_same_cover (F G : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t) (hG : Continuous G)
    (L M : List (ℝ × ℝ))
    (hL : ∀ ab ∈ L, ab.1 ≤ ab.2)
    (hM : ∀ ab ∈ M, ab.1 ≤ ab.2)
    (dL : L.Pairwise (fun ab cd => ab.2 ≤ cd.1 ∨ cd.2 ≤ ab.1))
    (dM : M.Pairwise (fun ab cd => ab.2 ≤ cd.1 ∨ cd.2 ≤ ab.1))
    (hc : closedCover L = closedCover M) : endpointSum F L = endpointSum F M := by
  rw [endpointSum_eq_integral F G hF hG L hL dL,
    endpointSum_eq_integral F G hF hG M hM dM, hc]
end
section
open HardSphereB5.Lean (Pt)
open Set MeasureTheory
private def HardSphereB5.Lean.Geometry.PathCore.E0.potential {c : Fin 4 → Pt} {i j : Fin 4} (D : PairArcDecomposition c i j) (t : ℝ) : ℝ :=
  inner ℝ (cross (c i) (c j)) (D.point t)
private def HardSphereB5.Lean.Geometry.PathCore.E0.angularDerivative {c : Fin 4 → Pt} {i j : Fin 4} (D : PairArcDecomposition c i j)
    (t : ℝ) : ℝ :=
  √(1-q c i j/4) *
    (-Real.sin t * inner ℝ (cross (c i) (c j)) D.U +
      Real.cos t * inner ℝ (cross (c i) (c j))
        (cross ((1 / dist (c i) (c j)) • (c j-c i)) D.U))
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.potential_hasDerivAt {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) (t : ℝ) :
    HasDerivAt (potential D) (angularDerivative D t) t := by
  let A := inner ℝ (cross (c i) (c j)) D.U
  let B := inner ℝ (cross (c i) (c j))
    (cross ((1 / dist (c i) (c j)) • (c j-c i)) D.U)
  let C := inner ℝ (cross (c i) (c j)) ((1/2 : ℝ) • (c i+c j))
  have he : potential D = fun t => C + √(1-q c i j/4) * (Real.cos t*A+Real.sin t*B) := by
    funext t
    simp only [potential, PairArcDecomposition.point, inner_add_right, real_inner_smul_right]
    dsimp [A, B, C]
    rw [real_inner_smul_right, inner_add_right]
  rw [he]
  convert ((((Real.hasDerivAt_cos t).mul_const A).add
    ((Real.hasDerivAt_sin t).mul_const B)).const_mul √(1-q c i j/4)).const_add C using 1 <;>
    first | rfl | simp [angularDerivative, A, B]
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.angularDerivative_continuous {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) : Continuous (angularDerivative D) := by
  unfold angularDerivative
  fun_prop
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.closedCover_eq {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) :
    EndpointIntervals.closedCover D.intervals =
      Icc (0:ℝ) (2*Real.pi) ∩ {t | D.point t ∈ Kset c} := by
  ext t
  constructor
  · rintro ⟨ab, hab, ht⟩
    obtain ⟨ha, hablt, hb⟩ := D.bounds ab hab
    have htb : t ∈ Icc (0:ℝ) (2*Real.pi) := ⟨ha.trans ht.1, ht.2.trans hb⟩
    refine ⟨htb, ?_⟩
    exact (D.cover t htb).mpr ⟨ab, hab, ht⟩
  · rintro ⟨ht, hu⟩
    exact (D.cover t ht).mp hu
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.pair_endpointSum_eq_integral {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) :
    (D.intervals.map (fun ab => inner ℝ (cross (c i) (c j))
      (D.point ab.2-D.point ab.1))).sum =
      ∫ t in Icc (0:ℝ) (2*Real.pi) ∩ {t | D.point t ∈ Kset c}, angularDerivative D t := by
  have he : (D.intervals.map (fun ab => inner ℝ (cross (c i) (c j))
      (D.point ab.2-D.point ab.1))).sum = EndpointIntervals.endpointSum (potential D) D.intervals := by
    simp only [EndpointIntervals.endpointSum, potential, inner_sub_right]
  rw [he, EndpointIntervals.endpointSum_eq_integral (potential D) (angularDerivative D)
    (potential_hasDerivAt D) (angularDerivative_continuous D) D.intervals
    (fun ab hab => (D.bounds ab hab).2.1.le) D.disjoint, closedCover_eq D]
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.inner_coords (x y : Pt) :
    inner ℝ x y = x 0*y 0+x 1*y 1+x 2*y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.cross_coords (x y : Pt) :
    cross x y = WithLp.toLp 2 ![x 1*y 2-x 2*y 1,
      x 2*y 0-x 0*y 2,x 0*y 1-x 1*y 0] := by
  simp [cross, SphereGeom.cross, cross_apply]
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.oriented_cross_sum (p q r x : Pt) (ε : ℝ) :
    ε*(inner ℝ (cross p q) x-inner ℝ (cross p r) x+inner ℝ (cross q r) x) =
      ε*inner ℝ (cross (q-p) (r-p)) x := by
  simp only [inner_coords, cross_coords]
  simp
  ring_nf
  simp
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.cross_perp_left (v w : Pt) : inner ℝ (cross v w) v = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.cross_perp_right (v w : Pt) : inner ℝ (cross v w) w = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.signed_vertex_algebra (p q r o : Pt) (ε α : ℝ)
    (hε : ε=1 ∨ ε= -1) (ho : inner ℝ (cross (q-p) (r-p)) o = 0) :
    ε*(inner ℝ (cross p q) (p+o+(ε*α)•cross (q-p) (r-p)) -
       inner ℝ (cross p r) (p+o+(ε*α)•cross (q-p) (r-p)) +
       inner ℝ (cross q r) (p+o+(ε*α)•cross (q-p) (r-p))) =
      α*‖cross (q-p) (r-p)‖^2 + ε*inner ℝ (cross (q-p) (r-p)) p := by
  rw [oriented_cross_sum, inner_add_right, inner_add_right, real_inner_smul_right,
    ho, add_zero, real_inner_self_eq_norm_sq]
  rcases hε with rfl | rfl <;> ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E0.faceCircRel_perp (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (cross (c j-c i) (c k-c i)) (faceCircRel c i j k) = 0 := by
  simp only [faceCircRel, inner_add_right, real_inner_smul_right,
    cross_perp_left, cross_perp_right, mul_zero, add_zero]
end
section
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore.E0
open Set MeasureTheory
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.inner_symm (x y : Pt) : inner ℝ x y = inner ℝ y x := by
  rw [inner_coords, inner_coords]
  ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.gram_resolution (v w x : Pt) :
    (inner ℝ v v * inner ℝ w w - (inner ℝ v w)^2) • x =
      (inner ℝ w w * inner ℝ v x - inner ℝ v w * inner ℝ w x) • v +
      (inner ℝ v v * inner ℝ w x - inner ℝ v w * inner ℝ v x) • w +
      inner ℝ (cross v w) x • cross v w := by
  simp only [inner_coords]
  ext i
  fin_cases i <;> simp [cross_coords] <;> ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.cross_square (v w : Pt) :
    inner ℝ (cross v w) (cross v w) =
      inner ℝ v v * inner ℝ w w - (inner ℝ v w)^2 := by
  simp only [inner_coords, cross_coords]
  simp
  ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.cross_combination (n u v : Pt) (a b : ℝ) :
    cross n (a • u + b • v) = a • cross n u + b • cross n v := by
  ext i
  fin_cases i <;> simp [cross_coords] <;> ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.cross_double (n u : Pt) :
    cross n (cross n u) = inner ℝ n u • n - inner ℝ n n • u := by
  simp only [inner_coords]
  ext i
  fin_cases i <;> simp [cross_coords] <;> ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.exists_angle (a b : ℝ) (hab : a^2+b^2=1) :
    ∃ t : ℝ, Real.cos t = a ∧ Real.sin t = b := by
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg b]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hs : Real.sqrt (1-a^2) = |b| := by
    have heq : 1-a^2=b^2 := by linarith
    rw [heq, Real.sqrt_sq_eq_abs]
  by_cases hb : 0 ≤ b
  · refine ⟨Real.arccos a, Real.cos_arccos ha1 ha2, ?_⟩
    rw [Real.sin_arccos, hs, abs_of_nonneg hb]
  · refine ⟨-Real.arccos a, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos ha1 ha2]
    · rw [Real.sin_neg, Real.sin_arccos, hs, abs_of_neg (lt_of_not_ge hb), neg_neg]
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.charts_eq_shift {c : Fin 4 → Pt} {i j : Fin 4}
    (hcij : c i ≠ c j) (D E : PairArcDecomposition c i j) :
    ∃ θ : ℝ, ∀ t : ℝ, E.point t = D.point (t+θ) := by
  let n : Pt := (1 / dist (c i) (c j)) • (c j-c i)
  let v : Pt := cross n D.U
  let a : ℝ := inner ℝ D.U E.U
  let b : ℝ := inner ℝ v E.U
  have hd : 0 < dist (c i) (c j) := dist_pos.mpr hcij
  have hn : ‖n‖ = 1 := by
    have hdN : ‖c j-c i‖ = dist (c i) (c j) := by
      calc
        ‖c j-c i‖ = dist (c j) (c i) := (dist_eq_norm (c j) (c i)).symm
        _ = dist (c i) (c j) := dist_comm _ _
    dsimp [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hd), hdN]
    exact div_mul_cancel₀ 1 hd.ne'
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have huu : inner ℝ D.U D.U = 1 := by rw [real_inner_self_eq_norm_sq, D.U_norm]; norm_num
  have hww : inner ℝ E.U E.U = 1 := by rw [real_inner_self_eq_norm_sq, E.U_norm]; norm_num
  have hnu : inner ℝ n D.U = 0 := by
    dsimp [n]
    rw [real_inner_smul_left, inner_symm (c j-c i) D.U, D.U_perp, mul_zero]
  have hnw : inner ℝ n E.U = 0 := by
    dsimp [n]
    rw [real_inner_smul_left, inner_symm (c j-c i) E.U, E.U_perp, mul_zero]
  have huv : inner ℝ D.U v = 0 := (inner_symm D.U v).trans (cross_perp_right n D.U)
  have hvu : inner ℝ v D.U = 0 := cross_perp_right n D.U
  have hvv : inner ℝ v v = 1 := by
    dsimp [v]
    rw [cross_square, hnn, huu, hnu]
    norm_num
  have hrepr : E.U = a • D.U + b • v := by
    have h := gram_resolution n D.U E.U
    simpa only [hnn, huu, hnu, hnw, one_mul, zero_pow (by decide : 2 ≠ 0),
      sub_zero, zero_sub, mul_zero, zero_mul, zero_smul, one_smul, zero_add] using h
  have hab : a^2+b^2=1 := by
    rw [hrepr] at hww
    simpa only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, huu, huv, hvu, hvv, mul_one, mul_zero, add_zero, zero_add,
      ← pow_two] using hww
  obtain ⟨θ, hcos, hsin⟩ := exists_angle a b hab
  have hnV : cross n v = -D.U := by
    dsimp [v]
    rw [cross_double, hnu, hnn, zero_smul, one_smul, zero_sub]
  have hEV : cross n E.U = -b • D.U + a • v := by
    rw [hrepr, cross_combination, hnV]
    dsimp [v]
    module
  refine ⟨θ, fun t => ?_⟩
  simp only [PairArcDecomposition.point]
  change (1/2:ℝ) • (c i+c j) + √(1-q c i j/4) •
      (Real.cos t • E.U + Real.sin t • cross n E.U) =
    (1/2:ℝ) • (c i+c j) + √(1-q c i j/4) •
      (Real.cos (t+θ) • D.U + Real.sin (t+θ) • v)
  rw [hEV, hrepr, Real.cos_add, Real.sin_add, hcos, hsin]
  module
end
section
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore.E0
open Set MeasureTheory
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.point_continuous {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) : Continuous D.point := by
  unfold PairArcDecomposition.point
  fun_prop
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.retained_measurable {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) : MeasurableSet {t | D.point t ∈ Kset c} := by
  have hK : IsClosed (Kset c) := by
    unfold Kset body
    exact isClosed_iInter fun j => isClosed_iInter fun _ => Metric.isClosed_closedBall
  exact (hK.preimage (point_continuous D)).measurableSet
private def HardSphereB5.Lean.Geometry.PathCore.E3.density {c : Fin 4 → Pt} {i j : Fin 4} (D : PairArcDecomposition c i j) : ℝ → ℝ :=
  ({t | D.point t ∈ Kset c} : Set ℝ).indicator (angularDerivative D)
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.density_periodic {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) : Function.Periodic (density D) (2*Real.pi) := by
  classical
  intro t
  have hp : D.point (t+2*Real.pi) = D.point t := by
    simp only [PairArcDecomposition.point, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hg : angularDerivative D (t+2*Real.pi) = angularDerivative D t := by
    simp only [angularDerivative, Real.cos_add_two_pi, Real.sin_add_two_pi]
  change (if D.point (t+2*Real.pi) ∈ Kset c then angularDerivative D (t+2*Real.pi) else 0) =
    (if D.point t ∈ Kset c then angularDerivative D t else 0)
  rw [hp, hg]
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.derivative_shift {c : Fin 4 → Pt} {i j : Fin 4}
    (D E : PairArcDecomposition c i j) (θ : ℝ)
    (he : ∀ t : ℝ, E.point t = D.point (t+θ)) (t : ℝ) :
    angularDerivative E t = angularDerivative D (t+θ) := by
  have hp : (fun x : ℝ => potential D (x+θ)) = potential E := by
    funext x
    simp only [potential, he x]
  have hh : HasDerivAt (fun x : ℝ => potential D (x+θ)) (angularDerivative D (t+θ)) t := by
    convert (potential_hasDerivAt D (t+θ)).comp t ((hasDerivAt_id t).add_const θ) using 1 <;>
      first | rfl | simp only [mul_one]
  rw [hp] at hh
  exact (potential_hasDerivAt E t).unique hh
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.density_shift {c : Fin 4 → Pt} {i j : Fin 4}
    (D E : PairArcDecomposition c i j) (θ : ℝ)
    (he : ∀ t : ℝ, E.point t = D.point (t+θ)) (t : ℝ) :
    density E t = density D (t+θ) := by
  classical
  change (if E.point t ∈ Kset c then angularDerivative E t else 0) =
    (if D.point (t+θ) ∈ Kset c then angularDerivative D (t+θ) else 0)
  rw [he t, derivative_shift D E θ he t]
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.pair_endpointSum_eq_period_integral {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) :
    (D.intervals.map (fun ab => inner ℝ (cross (c i) (c j))
      (D.point ab.2-D.point ab.1))).sum =
      ∫ t in (0:ℝ)..(2*Real.pi), density D t := by
  rw [pair_endpointSum_eq_integral D]
  change (∫ t in Icc (0:ℝ) (2*Real.pi) ∩ {t | D.point t ∈ Kset c}, angularDerivative D t) =
    ∫ t in (0:ℝ)..(2*Real.pi), density D t
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_indicator (retained_measurable D)).symm
private theorem HardSphereB5.Lean.Geometry.PathCore.E3.pair_endpointSum_eq_of_centers_ne {c : Fin 4 → Pt} {i j : Fin 4}
    (hcij : c i ≠ c j) (D E : PairArcDecomposition c i j) :
    (D.intervals.map (fun ab => inner ℝ (cross (c i) (c j))
      (D.point ab.2-D.point ab.1))).sum =
    (E.intervals.map (fun ab => inner ℝ (cross (c i) (c j))
      (E.point ab.2-E.point ab.1))).sum := by
  obtain ⟨θ, he⟩ := charts_eq_shift hcij D E
  calc
    _ = ∫ t in (0:ℝ)..(2*Real.pi), density D t := pair_endpointSum_eq_period_integral D
    _ = ∫ t in θ..θ+2*Real.pi, density D t := by
      simpa only [zero_add] using (density_periodic D).intervalIntegral_add_eq 0 θ
    _ = ∫ t in (0:ℝ)..(2*Real.pi), density E t := by
      have hdens : density E = fun t : ℝ => density D (t+θ) :=
        funext (density_shift D E θ he)
      rw [hdens, intervalIntegral.integral_comp_add_right]
      simp only [zero_add, add_comm θ]
    _ = _ := (pair_endpointSum_eq_period_integral E).symm
end
section
open HardSphereB5.Lean (Pt)
private theorem HardSphereB5.Lean.Geometry.PathCore.pair_endpointSum_eq_of_decomposition {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j)
    (D E : PairArcDecomposition c i j) :
    (D.intervals.map (fun ab => inner ℝ (cross (c i) (c j))
      (D.point ab.2-D.point ab.1))).sum =
    (E.intervals.map (fun ab => inner ℝ (cross (c i) (c j))
      (E.point ab.2-E.point ab.1))).sum := by
  by_cases hcij : c i = c j
  · have hz : cross (c i) (c j) = 0 := by
      rw [hcij]
      ext k
      fin_cases k <;> simp [E0.cross_coords] <;> ring
    simp [hz]
  · exact E3.pair_endpointSum_eq_of_centers_ne hcij D E
end
noncomputable section
open MeasureTheory Real
section
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace Classical
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.inner_coords (x y : Pt) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1,
      v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := by
  simp [cross, SphereGeom.cross, cross_apply]
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.inner_cross_left (v w : Pt) : inner ℝ (cross v w) v = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.inner_cross_right (v w : Pt) : inner ℝ (cross v w) w = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cross_norm_sq (v w : Pt) :
    inner ℝ (cross v w) (cross v w) = ‖v‖ ^ 2 * ‖w‖ ^ 2 - inner ℝ v w ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.triangle_cross_cycle (a b d : Pt) :
    cross a b + cross b d + cross d a = cross (b-a) (d-a) := by
  ext j
  fin_cases j <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.qnorm (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = ‖c j - c i‖ ^ 2 := by
  simp [q, dist_eq_norm, norm_sub_rev]
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.face_normal_sq (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (cross (c j - c i) (c k - c i)) (cross (c j - c i) (c k - c i)) =
      Deltaf c i j k / 4 := by
  have hs := norm_sub_sq_real (c j-c i) (c k-c i)
  have he : (c j-c i)-(c k-c i) = c j-c k := by abel
  rw [he] at hs
  rw [cross_norm_sq, Deltaf, DeltaT, qnorm c i j, qnorm c i k]
  have hq : q c j k = ‖c j - c k‖ ^ 2 := rfl
  rw [hq]
  nlinarith [hs]
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.normal_face_center (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (cross (c j - c i) (c k - c i)) (faceCircRel c i j k) = 0 := by
  simp only [faceCircRel, inner_add_right, real_inner_smul_right,
    inner_cross_left, inner_cross_right, mul_zero, zero_add]
private theorem HardSphereB5.Lean.Geometry.PathCore.E6.triple_signed_contribution {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ε * inner ℝ (cross (c i) (c j) + cross (c j) (c k) + cross (c k) (c i))
      (triplePoint c i j k ε) =
      ε * inner ℝ (cross (c j-c i) (c k-c i)) (c i) + √(Qf c i j k) / 2 := by
  have hD : Deltaf c i j k ≠ 0 := ((tetrahedron_metric hc).2.2.2.1 i j k hij hik hjk).ne'
  rw [triangle_cross_cycle, triplePoint, inner_add_right, inner_add_right,
    real_inner_smul_right, normal_face_center, face_normal_sq]
  rcases hε with rfl | rfl <;> field_simp [hD] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.tetrahedron_face_alternating (c : Fin 4 → Pt) :
    -inner ℝ (cross (c 2-c 1) (c 3-c 1)) (c 1) +
      inner ℝ (cross (c 2-c 0) (c 3-c 0)) (c 0) -
      inner ℝ (cross (c 1-c 0) (c 3-c 0)) (c 0) +
      inner ℝ (cross (c 1-c 0) (c 2-c 0)) (c 0) =
      -det3 (c 1-c 0) (c 2-c 0) (c 3-c 0) := by
  simp only [det3, inner_coords, cross_coords]
  simp
  ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E6.face_signed_planes (c : Fin 4 → Pt) :
    (∑ l : Fin 4,
      Real.sign (det3 (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1) (c l - c (faceVerts l).1)) *
      inner ℝ (cross (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1)) (c (faceVerts l).1)) =
      -|det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)| := by
  let d := det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)
  have hd0 : det3 (c 2-c 1) (c 3-c 1) (c 0-c 1) = -d := by
    dsimp [d, det3]
    simp only [inner_coords, cross_coords]
    simp
    ring
  have hd1 : det3 (c 2-c 0) (c 3-c 0) (c 1-c 0) = d := by
    dsimp [d, det3]
    simp only [inner_coords, cross_coords]
    simp
    ring
  have hd2 : det3 (c 1-c 0) (c 3-c 0) (c 2-c 0) = -d := by
    dsimp [d, det3]
    simp only [inner_coords, cross_coords]
    simp
    ring
  have hsum := tetrahedron_face_alternating c
  change -inner ℝ (cross (c 2-c 1) (c 3-c 1)) (c 1) +
    inner ℝ (cross (c 2-c 0) (c 3-c 0)) (c 0) -
    inner ℝ (cross (c 1-c 0) (c 3-c 0)) (c 0) +
    inner ℝ (cross (c 1-c 0) (c 2-c 0)) (c 0) = -d at hsum
  have hsign : Real.sign d * d = |d| := by
    rcases lt_trichotomy d 0 with hn | hz | hp
    · rw [Real.sign_of_neg hn, abs_of_neg hn]
      ring
    · rw [hz]
      simp
    · rw [Real.sign_of_pos hp, abs_of_pos hp, one_mul]
  rw [Fin.sum_univ_four]
  change Real.sign (det3 (c 2-c 1) (c 3-c 1) (c 0-c 1)) *
      inner ℝ (cross (c 2-c 1) (c 3-c 1)) (c 1) +
    Real.sign (det3 (c 2-c 0) (c 3-c 0) (c 1-c 0)) *
      inner ℝ (cross (c 2-c 0) (c 3-c 0)) (c 0) +
    Real.sign (det3 (c 1-c 0) (c 3-c 0) (c 2-c 0)) *
      inner ℝ (cross (c 1-c 0) (c 3-c 0)) (c 0) +
    Real.sign d * inner ℝ (cross (c 1-c 0) (c 2-c 0)) (c 0) = -|d|
  rw [hd0, hd1, hd2]
  simp only [Real.sign_neg]
  calc
    _ = Real.sign d * (-d) := by nlinarith [congrArg (fun t : ℝ => Real.sign d * t) hsum]
    _ = -|d| := by rw [mul_neg, hsign]
private theorem HardSphereB5.Lean.Geometry.PathCore.E6.face_signed_planes_path {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) :
    (∑ l : Fin 4,
      Real.sign (det3 (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1) (c l - c (faceVerts l).1)) *
      inner ℝ (cross (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1)) (c (faceVerts l).1)) =
      -√(Hpoly X Y s) / 2 := by
  rw [face_signed_planes]
  have hsq := (tetrahedron_metric hc).2.2.2.2
  have habs : |det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)| = √(Hpoly X Y s) / 2 := by
    nlinarith [sq_abs (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)),
      Real.sq_sqrt hc.H_pos.le, abs_nonneg (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)),
      Real.sqrt_nonneg (Hpoly X Y s)]
  rw [habs]
  ring
end
section
open HardSphereB5.Lean (Pt)
open scoped Classical RealInnerProductSpace
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cross_cross_identity (v w z : Pt) :
    cross v (cross w z) = inner ℝ v z • w - inner ℝ v w • z := by
  ext k
  fin_cases k <;> simp [cross_coords, inner_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cross_triple_identity (v w z : Pt) : inner ℝ v (cross w z) = inner ℝ (cross v w) z := by
  simp only [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cross_smul_left (s : ℝ) (v w : Pt) : cross (s • v) w = s • cross v w := by
  ext k
  fin_cases k <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cross_smul_right (s : ℝ) (v w : Pt) : cross v (s • w) = s • cross v w := by
  ext k
  fin_cases k <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cross_add_right (v w z : Pt) : cross v (w+z) = cross v w + cross v z := by
  ext k
  fin_cases k <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.point_derivative (c : Fin 4 → Pt) (i j : Fin 4) (D : PairArcDecomposition c i j)
    (hd : 0 < dist (c i) (c j)) (t : ℝ) :
    HasDerivAt D.point
      (cross ((1/dist (c i) (c j)) • (c j-c i))
        (D.point t-(1/2:ℝ) • (c i+c j))) t := by
  let n := (1/dist (c i) (c j)) • (c j-c i)
  have hnn : inner ℝ n n = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hunit : ‖n‖ = 1 := by
      dsimp [n]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd),
        ← dist_eq_norm, dist_comm (c j) (c i), one_div_mul_cancel hd.ne']
    rw [hunit];norm_num
  have hnu : inner ℝ n D.U = 0 := by
    dsimp [n]
    rw [real_inner_smul_left, real_inner_comm D.U (c j-c i), D.U_perp, mul_zero]
  have hcc : cross n (cross n D.U) = -D.U := by
    rw [cross_cross_identity, hnu, hnn]
    simp
  have hbase : HasDerivAt D.point
      (√(1-q c i j/4) • (-Real.sin t • D.U + Real.cos t • cross n D.U)) t := by
    unfold PairArcDecomposition.point
    convert ((((Real.hasDerivAt_cos t).smul_const D.U).add
      ((Real.hasDerivAt_sin t).smul_const (cross n D.U))).const_smul √(1-q c i j/4)).const_add ((1/2:ℝ) • (c i+c j)) using 1 <;> first | rfl | (funext x; rfl)
  convert hbase using 1
  rw [PairArcDecomposition.point, add_sub_cancel_left, cross_smul_right,
    cross_add_right, cross_smul_right, cross_smul_right, hcc]
  dsimp only [n]
  module
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.cut_hasDerivAt (c : Fin 4 → Pt) (i j k : Fin 4) (D : PairArcDecomposition c i j)
    (hd : 0 < dist (c i) (c j)) (t : ℝ) :
    HasDerivAt (fun t => dist (D.point t) (c k)^2 - 1)
      ((2/dist (c i) (c j)) * det3 (c j-c i) (c k-c i) (D.point t-c i)) t := by
  let d := dist (c i) (c j)
  let n := (1/d) • (c j-c i)
  let m := (1/2:ℝ) • (c i+c j)
  have hp := (point_derivative c i j D hd t).sub_const (c k)
  have hsq := hp.inner ℝ hp
  have he : (fun t => inner ℝ (D.point t-c k) (D.point t-c k) - 1) =
      (fun t => dist (D.point t) (c k)^2-1) := by
    funext t
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm]
  have hder := hsq.sub_const 1
  rw [he] at hder
  convert hder using 1
  all_goals first | rfl | (simp [det3, inner_coords, cross_coords]; ring)
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.triple_root_det {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) (ε : ℝ) :
    det3 (c j-c i) (c k-c i) (triplePoint c i j k ε-c i) = ε*√(Qf c i j k)/2 := by
  have hD : Deltaf c i j k ≠ 0 := ((tetrahedron_metric hc).2.2.2.1 i j k hij hik hjk).ne'
  have he : triplePoint c i j k ε-c i = faceCircRel c i j k +
      (ε*2*√(Qf c i j k)/Deltaf c i j k) • cross (c j-c i) (c k-c i) := by
    dsimp [triplePoint];abel
  rw [he]
  simp only [det3, inner_add_right, normal_face_center, real_inner_smul_right,
    face_normal_sq, zero_add]
  field_simp [hD]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E6.triple_cut_sign {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) (ε : ℝ) (hε : ε=1 ∨ ε= -1)
    (hd : 0 < dist (c i) (c j)) :
    Real.sign ((2/dist (c i) (c j))*det3 (c j-c i) (c k-c i)
      (triplePoint c i j k ε-c i)) = ε := by
  have hQ : 0 < Qf c i j k := HardSphereB5.Lean.Geometry.pathFaceQ_pos c X Y s
    hc.q01 hc.q02 hc.q03 hc.q12 hc.q13 hc.q23 hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
    hc.H_pos i j k hij hik hjk
  have hp : 0 < √(Qf c i j k)/dist (c i) (c j) := div_pos (Real.sqrt_pos.mpr hQ) hd
  rw [triple_root_det hc i j k hij hik hjk]
  have he : (2/dist (c i) (c j))*(ε*√(Qf c i j k)/2) = ε*(√(Qf c i j k)/dist (c i) (c j)) := by ring
  rw [he]
  rcases hε with rfl | rfl
  · simpa using Real.sign_of_pos hp
  · simpa using Real.sign_of_neg (neg_neg_of_pos hp)
end
section
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore.E6
open scoped Classical RealInnerProductSpace
private lemma HardSphereB5.Lean.Geometry.PathCore.E1.two_sphere_dot (x a b : Pt) (hxa : dist x a = 1) (hxb : dist x b = 1) :
    inner ℝ (b-a) (x-a) = q (fun _ : Fin 4 => a) 0 0 + ‖b-a‖^2/2 := by
  have hu : ‖x-a‖ = 1 := by simpa only [dist_eq_norm] using hxa
  have huv : ‖(x-a)-(b-a)‖ = 1 := by
    have he : (x-a)-(b-a)=x-b := by abel
    simpa only [he, dist_eq_norm] using hxb
  have hh := norm_sub_sq_real (x-a) (b-a)
  rw [hu, huv] at hh
  simp only [q, dist_self, zero_pow (by decide : 2≠0), zero_add]
  rw [real_inner_comm (b-a) (x-a)] at hh
  nlinarith
private lemma HardSphereB5.Lean.Geometry.PathCore.E1.determinant_gram (v w u : Pt) :
    (det3 v w u)^2 = inner ℝ v v*inner ℝ w w*inner ℝ u u +
      2*inner ℝ v w*inner ℝ v u*inner ℝ w u -
      inner ℝ v v*(inner ℝ w u)^2-inner ℝ w w*(inner ℝ v u)^2-
      inner ℝ u u*(inner ℝ v w)^2 := by
  simp only [det3, inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E1.gram_resolution (v w u : Pt) :
    (inner ℝ v v*inner ℝ w w-(inner ℝ v w)^2) • u =
      (inner ℝ w w*inner ℝ v u-inner ℝ v w*inner ℝ w u) • v +
      (inner ℝ v v*inner ℝ w u-inner ℝ v w*inner ℝ v u) • w +
      inner ℝ (cross v w) u • cross v w := by
  simp only [inner_coords]
  ext d
  fin_cases d <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E1.sphere_root_det_sq (c : Fin 4 → Pt) (i j k : Fin 4) (x : Pt)
    (hi : dist x (c i)=1) (hj : dist x (c j)=1) (hk : dist x (c k)=1) :
    (det3 (c j-c i) (c k-c i) (x-c i))^2 = Qf c i j k/4 := by
  have hunit : inner ℝ (x-c i) (x-c i) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hi];norm_num
  have hv := two_sphere_dot x (c i) (c j) hi hj
  have hw := two_sphere_dot x (c i) (c k) hi hk
  simp only [q, dist_self, zero_pow (by decide : 2≠0), zero_add] at hv hw
  have hsub := norm_sub_sq_real (c j-c i) (c k-c i)
  have he : (c j-c i)-(c k-c i)=c j-c k := by abel
  rw [he] at hsub
  have hvw : inner ℝ (c j-c i) (c k-c i) = (q c i j+q c i k-q c j k)/2 := by
    rw [qnorm c i j, qnorm c i k]
    change _ = (‖c j-c i‖^2+‖c k-c i‖^2-‖c j-c k‖^2)/2
    nlinarith
  rw [determinant_gram, hunit, hv, hw, hvw, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, ← qnorm c i j, ← qnorm c i k]
  simp only [Qf, QT, DeltaT]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E1.point_eq_triplePoint_of_sign {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (x : Pt) (hi : dist x (c i)=1) (hj : dist x (c j)=1) (hk : dist x (c k)=1)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1)
    (hs : Real.sign (det3 (c j-c i) (c k-c i) (x-c i)) = ε) :
    x = triplePoint c i j k ε := by
  have hDpos := (tetrahedron_metric hc).2.2.2.1 i j k hij hik hjk
  have hQ : 0 < Qf c i j k := HardSphereB5.Lean.Geometry.pathFaceQ_pos c X Y s
    hc.q01 hc.q02 hc.q03 hc.q12 hc.q13 hc.q23 hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
    hc.H_pos i j k hij hik hjk
  have hdet : det3 (c j-c i) (c k-c i) (x-c i)=ε*√(Qf c i j k)/2 := by
    have hh := sphere_root_det_sq c i j k x hi hj hk
    rcases hε with rfl | rfl
    · have hp : 0 < det3 (c j-c i) (c k-c i) (x-c i) := by
        by_contra h
        simp only [Real.sign, if_neg h] at hs
        split_ifs at hs <;> norm_num at hs
      nlinarith [Real.sq_sqrt hQ.le, Real.sqrt_nonneg (Qf c i j k)]
    · have hn : det3 (c j-c i) (c k-c i) (x-c i) < 0 := by
        by_contra h
        simp only [Real.sign, if_neg h] at hs
        split_ifs at hs <;> norm_num at hs
      nlinarith [Real.sq_sqrt hQ.le, Real.sqrt_nonneg (Qf c i j k)]
  let p := triplePoint c i j k ε
  have hp := (face_circumcenter_identities hc i j k hij hik hjk).2.2.2 ε hε
  have hpi : dist p (c i)=1 := hp i (by simp)
  have hpj : dist p (c j)=1 := hp j (by simp)
  have hpk : dist p (c k)=1 := hp k (by simp)
  have hxv := two_sphere_dot x (c i) (c j) hi hj
  have hpv := two_sphere_dot p (c i) (c j) hpi hpj
  have hxw := two_sphere_dot x (c i) (c k) hi hk
  have hpw := two_sphere_dot p (c i) (c k) hpi hpk
  have hv : inner ℝ (c j-c i) (x-p)=0 := by
    have he : x-p=(x-c i)-(p-c i) := by abel
    rw [he, inner_sub_right, hxv, hpv, sub_self]
  have hw : inner ℝ (c k-c i) (x-p)=0 := by
    have he : x-p=(x-c i)-(p-c i) := by abel
    rw [he, inner_sub_right, hxw, hpw, sub_self]
  have hn : inner ℝ (cross (c j-c i) (c k-c i)) (x-p)=0 := by
    have he : x-p=(x-c i)-(p-c i) := by abel
    rw [he, inner_sub_right]
    change det3 (c j-c i) (c k-c i) (x-c i) -
      det3 (c j-c i) (c k-c i) (p-c i)=0
    rw [hdet, triple_root_det hc i j k hij hik hjk]
    exact sub_self _
  have hg := gram_resolution (c j-c i) (c k-c i) (x-p)
  rw [hv, hw, hn] at hg
  simp only [mul_zero, sub_self, zero_smul, add_zero] at hg
  have hh : inner ℝ (c j-c i) (c j-c i)*inner ℝ (c k-c i) (c k-c i)-
      (inner ℝ (c j-c i) (c k-c i))^2 = Deltaf c i j k/4 := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← cross_norm_sq, face_normal_sq]
  rw [hh] at hg
  have hcoef : Deltaf c i j k/4 ≠ 0 := div_ne_zero hDpos.ne' (by norm_num)
  have hz : x-p=0 := (smul_eq_zero.mp hg).resolve_left hcoef
  exact sub_eq_zero.mp hz
end
section
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem HardSphereB5.Lean.Geometry.PathCore.E5.aligned_model_exists (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    ∃ M : P3PairCosModel c i j,
      perpProj (c j-c i) (c (oth1 i j)-c i) =
        ‖perpProj (c j-c i) (c (oth1 i j)-c i)‖ • M.e 0 ∧
      perpProj (c j-c i) (c (oth2 i j)-c i) =
        ‖perpProj (c j-c i) (c (oth2 i j)-c i)‖ •
          (Real.cos (phiE c i j) • M.e 0 + Real.sin (phiE c i j) • M.e 1) := by
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
  have hm : ∃ M : P3PairCosModel c i j, M.e = e := by
    refine ⟨⟨e, he, hp, hd0, hd2, hA, hB, p3_phi_range hc i j hij, ?_, ?_, ?_, ?_⟩, rfl⟩
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
  obtain ⟨M, heq⟩ := hm
  refine ⟨M, ?_, ?_⟩
  · simpa only [heq] using hu
  · simpa only [heq] using hv
private lemma HardSphereB5.Lean.Geometry.PathCore.E5.model_det {i j k : Fin 4} (M : P3PairCosModel c i j) (θ u σ : ℝ)
    (hσ : σ=1 ∨ σ= -1)
    (hcross : cross ((1/dist (c i) (c j)) • (c j-c i)) (M.e 0) = σ • M.e 1)
    (haligned : perpProj (c j-c i) (c k-c i) =
      ‖perpProj (c j-c i) (c k-c i)‖ • (Real.cos θ • M.e 0 + Real.sin θ • M.e 1)) :
    det3 (c j-c i) (c k-c i) (M.point u-c i) =
      σ * dist (c i) (c j) * ‖perpProj (c j-c i) (c k-c i)‖ *
        Real.sqrt (1-q c i j/4) * Real.sin (u-θ) := by
  let v := c j-c i
  let w := c k-c i
  let d := dist (c i) (c j)
  let n := (1/d) • v
  have hdn : d • n = v := by
    dsimp [n]
    rw [smul_smul, mul_one_div_cancel (show d ≠ 0 from M.dist_pos.ne'), one_smul]
  have hnorm : ‖n‖ = 1 := by
    dsimp [n, d, v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr M.dist_pos),
      ← dist_eq_norm, dist_comm (c j) (c i), one_div_mul_cancel M.dist_pos.ne']
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hnorm]; norm_num
  have hn0 : inner ℝ n (M.e 0) = 0 := by
    dsimp [n, v]
    rw [real_inner_smul_left, M.perp 0, mul_zero]
  have hcc : cross n (cross n (M.e 0)) = -(M.e 0) := by
    rw [E6.cross_cross_identity, hn0, hnn]
    simp
  have hc1 : cross n (M.e 1) = -σ • M.e 0 := by
    change cross n (cross n (M.e 0)) = -(M.e 0) at hcc
    change cross n (M.e 0) = σ • M.e 1 at hcross
    rw [hcross, E6.cross_smul_right] at hcc
    rcases hσ with rfl | rfl
    · simpa using hcc
    · simpa using congrArg Neg.neg hcc
  have hc0 : cross n (M.e 0) = σ • M.e 1 := hcross
  have hself : cross v v = 0 := by
    ext l; fin_cases l <;> simp [E6.cross_coords] <;> ring
  have hw : w = perpProj v w + (inner ℝ v w / inner ℝ v v) • v := by
    dsimp [perpProj]
    rw [real_inner_comm w v]
    abel
  have hcrossv (z : Pt) : cross v z = d • cross n z := by
    calc
      cross v z = cross (d • n) z := congrArg (fun y => cross y z) hdn.symm
      _ = d • cross n z := E6.cross_smul_left d n z
  have hcw : cross v w =
      d • (‖perpProj v w‖ •
        (Real.cos θ • (σ • M.e 1) + Real.sin θ • (-σ • M.e 0))) := by
    calc
      cross v w = cross v (perpProj v w) := by
        have hh := congrArg (fun y => cross v y) hw
        simpa only [E6.cross_add_right, E6.cross_smul_right, hself,
          smul_zero, add_zero] using hh
      _ = _ := by
        conv_lhs => rw [hcrossv, haligned, E6.cross_smul_right,
          E6.cross_add_right, E6.cross_smul_right,
          E6.cross_smul_right, hc0, hc1]
  have hp0 : inner ℝ (M.e 0) v = 0 := by rw [real_inner_comm]; exact M.perp 0
  have hp1 : inner ℝ (M.e 1) v = 0 := by rw [real_inner_comm]; exact M.perp 1
  have he00 : inner ℝ (M.e 0) (M.e 0) = 1 := by simpa using (orthonormal_iff_ite.mp M.ortho) 0 0
  have he01 : inner ℝ (M.e 0) (M.e 1) = 0 := by simpa using (orthonormal_iff_ite.mp M.ortho) 0 1
  have he10 : inner ℝ (M.e 1) (M.e 0) = 0 := by simpa using (orthonormal_iff_ite.mp M.ortho) 1 0
  have he11 : inner ℝ (M.e 1) (M.e 1) = 1 := by simpa using (orthonormal_iff_ite.mp M.ortho) 1 1
  have hpoint : M.point u-c i = (1/2:ℝ) • v + Real.sqrt (1-q c i j/4) •
      (Real.cos u • M.e 0 + Real.sin u • M.e 1) := by
    dsimp [P3PairCosModel.point, SphereGeom.circlePt, v]
    module
  change inner ℝ (cross v w) (M.point u-c i) = _
  rw [hcw, hpoint]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hp0, hp1, he00, he01, he10, he11]
  dsimp [d, v, w]
  rw [Real.sin_sub]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E5.model_root (hc : IsPathConfig c X Y s) {i j k : Fin 4} (hij : i≠j) (hik : i≠k)
    (hjk : j≠k) (M : P3PairCosModel c i j) (θ β σ : ℝ)
    (hβ0 : 0 < β) (hβπ : β < Real.pi) (hσ : σ=1 ∨ σ= -1)
    (hcross : cross ((1/dist (c i) (c j)) • (c j-c i)) (M.e 0) = σ • M.e 1)
    (haligned : perpProj (c j-c i) (c k-c i) =
      ‖perpProj (c j-c i) (c k-c i)‖ • (Real.cos θ • M.e 0 + Real.sin θ • M.e 1))
    (hsphere : ∀ u, M.point u ∈ Metric.sphere (c k) 1 ↔ Real.cos β = Real.cos (u-θ))
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
    M.point (θ+ε*β) = triplePoint c i j k (σ*ε) := by
  have hpair := p3_model_point_on_spheres c i j M (θ+ε*β)
  have hthird : dist (M.point (θ+ε*β)) (c k) = 1 := by
    apply Metric.mem_sphere.mp
    apply (hsphere _).mpr
    have he : θ+ε*β-θ = ε*β := by ring
    rw [he]
    rcases hε with rfl | rfl <;> simp [Real.cos_neg]
  have hQ := P9_Qf_pos hc i j k hij hik hjk
  have hq := p3_q_pos_lt_four hc i j hij
  have hp : 0 < ‖perpProj (c j-c i) (c k-c i)‖ :=
    (p3_beta_cos_ratio c i j k hq.1 hq.2 hQ).1
  let p := dist (c i) (c j) * ‖perpProj (c j-c i) (c k-c i)‖ *
      Real.sqrt (1-q c i j/4) * Real.sin β
  have hpos : 0 < p := mul_pos (mul_pos (mul_pos M.dist_pos hp)
    (p3_pair_radius_pos hc i j hij)) (Real.sin_pos_of_pos_of_lt_pi hβ0 hβπ)
  have hdet : det3 (c j-c i) (c k-c i) (M.point (θ+ε*β)-c i) = (σ*ε)*p := by
    rw [model_det M θ (θ+ε*β) σ hσ hcross haligned]
    have he : θ+ε*β-θ = ε*β := by ring
    rw [he]
    dsimp [p]
    rcases hε with rfl | rfl <;> simp only [one_mul, neg_one_mul, Real.sin_neg] <;> ring
  have hsign : Real.sign (det3 (c j-c i) (c k-c i) (M.point (θ+ε*β)-c i)) = σ*ε := by
    rw [hdet]
    rcases hσ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      simp [Real.sign_of_pos hpos, Real.sign_of_neg (neg_neg_of_pos hpos)]
  have hσeps : σ*ε=1 ∨ σ*ε= -1 := by
    rcases hσ with rfl | rfl <;> rcases hε with rfl | rfl <;> norm_num
  exact E1.point_eq_triplePoint_of_sign hc i j k hij hik hjk
    (M.point (θ+ε*β)) (Metric.mem_sphere.mp hpair.1) (Metric.mem_sphere.mp hpair.2)
    hthird (σ*ε) hσeps hsign
private lemma HardSphereB5.Lean.Geometry.PathCore.E5.canonical_cover (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) (M : P3PairCosModel c i j) :
    ∀ t ∈ Set.Icc (0 : ℝ) (2*Real.pi), M.point (t-Real.pi) ∈ Kset c ↔
      ∃ ab ∈ CircleArc.RawPieces.intervals (betaA c i j (oth1 i j))
        (betaA c i j (oth2 i j)) (phiE c i j), t ∈ Set.Icc ab.1 ab.2 := by
  let a := betaA c i j (oth1 i j)
  let b := betaA c i j (oth2 i j)
  let φ := phiE c i j
  have ha0 : 0 < a := M.betaA_range.1
  have haπ : a < Real.pi := M.betaA_range.2
  have hb0 : 0 < b := M.betaB_range.1
  have hbπ : b < Real.pi := M.betaB_range.2
  have hφ0 : 0 < φ := M.phi_range.1
  have hφπ : φ < Real.pi := M.phi_range.2
  have hquad (u : ℝ) (hA : Real.cos u = Real.cos a)
      (hB : Real.cos (u-φ) = Real.cos b) : False := by
    have hpair := p3_model_point_on_spheres c i j M u
    have hsa := (M.sphereA u).mpr hA
    have hsb := (M.sphereB u).mpr hB
    apply P9_no_quadruple hc hP (M.point u)
    intro m
    rcases p3_indices_cover i j m hij with rfl | rfl | rfl | rfl
    · exact Metric.mem_sphere.mp hpair.1
    · exact Metric.mem_sphere.mp hpair.2
    · exact Metric.mem_sphere.mp hsa
    · exact Metric.mem_sphere.mp hsb
  have hnormal : a+b ≠ φ := by
    intro heq
    apply hquad a rfl
    have hsub : a-φ = -b := by linarith
    rw [hsub, Real.cos_neg]
  have hwrap : a+b+φ ≠ 2*Real.pi := by
    intro heq
    apply hquad (-a) (Real.cos_neg a)
    have hsub : -a-φ = b-2*Real.pi := by linarith
    rw [hsub, Real.cos_sub_two_pi]
  have hfirst (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2*Real.pi)) :
      Real.cos a ≤ Real.cos (t-Real.pi) ↔
      t-Real.pi ∈ Set.Icc (-a) a := by
    have habs : |t-Real.pi| ≤ Real.pi := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    constructor
    · intro hcos
      have hu : |t-Real.pi| ≤ a := by
        by_contra h
        have hc' := Real.cos_lt_cos_of_nonneg_of_le_pi ha0.le habs (lt_of_not_ge h)
        rw [Real.cos_abs] at hc'
        exact (not_lt_of_ge hcos) hc'
      exact abs_le.mp hu
    · intro hu
      have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (t-Real.pi)) haπ.le (abs_le.mpr hu)
      simpa only [Real.cos_abs] using hh
  have hpull (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2*Real.pi)) :
      M.point (t-Real.pi) ∈ Kset c ↔
      ((-a ≤ t-Real.pi ∧ t-Real.pi ≤ a) ∧
        ((φ-b ≤ t-Real.pi ∧ t-Real.pi ≤ φ+b) ∨
          t-Real.pi ≤ φ+b-2*Real.pi)) := by
    have hpair := p3_model_point_on_spheres c i j M (t-Real.pi)
    have hlocus := congrArg (fun S : Set Pt => M.point (t-Real.pi) ∈ S)
      (p3_pair_locus_eq c i j hij)
    simp only [Set.mem_inter_iff, hpair.1, hpair.2, true_and] at hlocus
    have hcutA : M.point (t-Real.pi) ∈ Metric.closedBall (c (oth1 i j)) 1 ↔
        t-Real.pi ∈ Set.Icc (-a) a := (M.ballA (t-Real.pi)).trans (hfirst t ht)
    rw [hlocus, hcutA]
    constructor
    · rintro ⟨hu, hball⟩
      have hmem : M.point (t-Real.pi) ∈ M.arcB := by
        rw [← p3_model_ballB_set c i j M]
        exact ⟨hpair, hball⟩
      exact ⟨hu, (CircleArc.periodicMembership
        ((1/2:ℝ) • (c i+c j)) M.e M.ortho (Real.sqrt (1-q c i j/4))
        (p3_pair_radius_pos hc i j hij) a b φ ha0 haπ hb0 hbπ hφ0 hφπ
        (t-Real.pi) hu).mp hmem⟩
    · rintro ⟨hu, hb⟩
      have hmem : M.point (t-Real.pi) ∈ M.arcB :=
        (CircleArc.periodicMembership
          ((1/2:ℝ) • (c i+c j)) M.e M.ortho (Real.sqrt (1-q c i j/4))
          (p3_pair_radius_pos hc i j hij) a b φ ha0 haπ hb0 hbπ hφ0 hφπ
          (t-Real.pi) hu).mpr hb
      rw [← p3_model_ballB_set c i j M] at hmem
      exact ⟨hu, hmem.2⟩
  intro t ht
  exact (hpull t ht).trans (CircleArc.RawPieces.cover a b φ ha0 haπ hb0 hbπ hφ0 hφπ
    hnormal hwrap t)
private lemma HardSphereB5.Lean.Geometry.PathCore.E5.model_noncoincidence (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    {i j : Fin 4} (hij : i≠j) (M : P3PairCosModel c i j) :
    let a := betaA c i j (oth1 i j)
    let b := betaA c i j (oth2 i j)
    let φ := phiE c i j
    a+b ≠ φ ∧ a+b+φ ≠ 2*Real.pi ∧ -a ≠ φ-b ∧ a ≠ φ+b := by
  dsimp only
  let a := betaA c i j (oth1 i j)
  let b := betaA c i j (oth2 i j)
  let φ := phiE c i j
  have hquad (u : ℝ) (hA : Real.cos u = Real.cos a)
      (hB : Real.cos (u-φ) = Real.cos b) : False := by
    have hpair := p3_model_point_on_spheres c i j M u
    have hsa := (M.sphereA u).mpr hA
    have hsb := (M.sphereB u).mpr hB
    apply P9_no_quadruple hc hP (M.point u)
    intro m
    rcases p3_indices_cover i j m hij with rfl | rfl | rfl | rfl
    · exact Metric.mem_sphere.mp hpair.1
    · exact Metric.mem_sphere.mp hpair.2
    · exact Metric.mem_sphere.mp hsa
    · exact Metric.mem_sphere.mp hsb
  constructor
  · intro h
    apply hquad a rfl
    have he : a-φ = -b := by linarith
    rw [he, Real.cos_neg]
  constructor
  · intro h
    apply hquad (-a) (Real.cos_neg a)
    have he : -a-φ = b-2*Real.pi := by linarith
    rw [he, Real.cos_sub_two_pi]
  constructor
  · intro h
    apply hquad (-a) (Real.cos_neg a)
    have he : -a-φ = -b := by linarith
    rw [he, Real.cos_neg]
  · intro h
    apply hquad a rfl
    have he : a-φ = b := by linarith
    rw [he]
private def HardSphereB5.Lean.Geometry.PathCore.E5.modelFourRoots {i j : Fin 4} (M : P3PairCosModel c i j) : ℝ :=
  (if M.point (betaA c i j (oth1 i j)) ∈ Kset c
    then inner ℝ (cross (c i) (c j)) (M.point (betaA c i j (oth1 i j))) else 0) -
  (if M.point (-betaA c i j (oth1 i j)) ∈ Kset c
    then inner ℝ (cross (c i) (c j)) (M.point (-betaA c i j (oth1 i j))) else 0) +
  (if M.point (phiE c i j + betaA c i j (oth2 i j)) ∈ Kset c
    then inner ℝ (cross (c i) (c j)) (M.point (phiE c i j + betaA c i j (oth2 i j))) else 0) -
  (if M.point (phiE c i j - betaA c i j (oth2 i j)) ∈ Kset c
    then inner ℝ (cross (c i) (c j)) (M.point (phiE c i j - betaA c i j (oth2 i j))) else 0)
private lemma HardSphereB5.Lean.Geometry.PathCore.E5.model_endpoint_sum (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    {i j : Fin 4} (hij : i≠j) (M : P3PairCosModel c i j) :
    CircleArc.RawPieces.endpointSum
      (fun t => inner ℝ (cross (c i) (c j)) (M.point (t-Real.pi)))
      (CircleArc.RawPieces.intervals (betaA c i j (oth1 i j))
        (betaA c i j (oth2 i j)) (phiE c i j)) = modelFourRoots M := by
  let a := betaA c i j (oth1 i j)
  let b := betaA c i j (oth2 i j)
  let φ := phiE c i j
  have hcutA (u : ℝ) : M.point u ∈ Metric.closedBall (c (oth1 i j)) 1 ↔
      CircleArc.RawPieces.periodicCap 0 a u := by
    apply (M.ballA u).trans
    simpa [CircleArc.RawPieces.periodicCap, Set.mem_Icc] using
      CircleArc.cos_cut_periodic_shift a 0 u M.betaA_range.1.le M.betaA_range.2.le
  have hcutB (u : ℝ) : M.point u ∈ Metric.closedBall (c (oth2 i j)) 1 ↔
      CircleArc.RawPieces.periodicCap φ b u := by
    apply (M.ballB u).trans
    simpa only [CircleArc.RawPieces.periodicCap, Set.mem_Icc, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using
      CircleArc.cos_cut_periodic_shift b φ u M.betaB_range.1.le M.betaB_range.2.le
  have hretA (u : ℝ) (hu : Real.cos u = Real.cos a) :
      M.point u ∈ Kset c ↔ CircleArc.RawPieces.periodicCap φ b u := by
    have hp := p3_model_point_on_spheres c i j M u
    have ha : M.point u ∈ Metric.closedBall (c (oth1 i j)) 1 := Metric.sphere_subset_closedBall ((M.sphereA u).mpr hu)
    have hh := congrArg (fun S : Set Pt => M.point u ∈ S) (p3_pair_locus_eq c i j hij)
    simp only [Set.mem_inter_iff, hp.1, hp.2, ha, true_and] at hh
    exact hh.to_iff.trans (hcutB u)
  have hretB (u : ℝ) (hu : Real.cos (u-φ) = Real.cos b) :
      M.point u ∈ Kset c ↔ CircleArc.RawPieces.periodicCap 0 a u := by
    have hp := p3_model_point_on_spheres c i j M u
    have hb : M.point u ∈ Metric.closedBall (c (oth2 i j)) 1 := Metric.sphere_subset_closedBall ((M.sphereB u).mpr hu)
    have hh := congrArg (fun S : Set Pt => M.point u ∈ S) (p3_pair_locus_eq c i j hij)
    simp only [Set.mem_inter_iff, hp.1, hp.2, hb, true_and, and_true] at hh
    exact hh.to_iff.trans (hcutA u)
  have hAp := hretA a rfl
  have hAm := hretA (-a) (Real.cos_neg a)
  have hBp := hretB (φ+b) (by rw [add_sub_cancel_left])
  have hBm := hretB (φ-b) (by
    have he : φ-b-φ = -b := by ring
    rw [he, Real.cos_neg])
  let F : ℝ → ℝ := fun t => inner ℝ (cross (c i) (c j)) (M.point (t-Real.pi))
  have hperiod : Function.Periodic F (2*Real.pi) := by
    intro t
    have he : t+2*Real.pi-Real.pi = (t-Real.pi)+2*Real.pi := by ring
    simp only [F, he, P3PairCosModel.point, SphereGeom.circlePt,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hn := model_noncoincidence hc hP hij M
  have hh := CircleArc.RawPieces.canonical_endpointSum_periodic F hperiod a b φ
    M.betaA_range.1 M.betaA_range.2 M.betaB_range.1 M.betaB_range.2 M.phi_range.1 M.phi_range.2
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  simp only [← hAp, ← hAm, ← hBp, ← hBm] at hh
  have he1 : Real.pi+a-Real.pi = a := by ring
  have he2 : Real.pi-a-Real.pi = -a := by ring
  have he3 : Real.pi+φ+b-Real.pi = φ+b := by ring
  have he4 : Real.pi+φ-b-Real.pi = φ-b := by ring
  simpa only [F, he1, he2, he3, he4, modelFourRoots] using hh
private lemma HardSphereB5.Lean.Geometry.PathCore.E5.model_four_roots_signed (hc : IsPathConfig c X Y s) {i j : Fin 4} (hij : i≠j)
    (M : P3PairCosModel c i j) (σ : ℝ) (hσ : σ=1 ∨ σ= -1)
    (hcross : cross ((1/dist (c i) (c j)) • (c j-c i)) (M.e 0) = σ • M.e 1)
    (halignedA : perpProj (c j-c i) (c (oth1 i j)-c i) =
      ‖perpProj (c j-c i) (c (oth1 i j)-c i)‖ • M.e 0)
    (halignedB : perpProj (c j-c i) (c (oth2 i j)-c i) =
      ‖perpProj (c j-c i) (c (oth2 i j)-c i)‖ •
        (Real.cos (phiE c i j) • M.e 0 + Real.sin (phiE c i j) • M.e 1)) :
    σ * modelFourRoots M =
      ∑ k ∈ (Finset.univ.erase i).erase j, ∑ ε ∈ ({-1,1} : Finset ℝ),
        if triplePoint c i j k ε ∈ Kset c then
          ε*inner ℝ (cross (c i) (c j)) (triplePoint c i j k ε) else 0 := by
  have hiA : i≠oth1 i j := by fin_cases i <;> fin_cases j <;> simp_all [oth1, oth2]
  have hjA : j≠oth1 i j := by fin_cases i <;> fin_cases j <;> simp_all [oth1, oth2]
  have hiB : i≠oth2 i j := by fin_cases i <;> fin_cases j <;> simp_all [oth1, oth2]
  have hjB : j≠oth2 i j := by fin_cases i <;> fin_cases j <;> simp_all [oth1, oth2]
  have hAB : oth1 i j≠oth2 i j := by fin_cases i <;> fin_cases j <;> simp_all [oth1, oth2]
  have hothers : (Finset.univ.erase i).erase j = {oth1 i j, oth2 i j} := by
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact hij rfl) | decide
  have ha' : perpProj (c j-c i) (c (oth1 i j)-c i) =
      ‖perpProj (c j-c i) (c (oth1 i j)-c i)‖ •
        (Real.cos (0 : ℝ) • M.e 0 + Real.sin (0 : ℝ) • M.e 1) := by simpa using halignedA
  have hAp : M.point (betaA c i j (oth1 i j)) = triplePoint c i j (oth1 i j) σ := by
    simpa only [zero_add, one_mul, mul_one] using
      model_root hc hij hiA hjA M 0 _ σ M.betaA_range.1 M.betaA_range.2 hσ hcross ha'
        (fun u => by simpa only [sub_zero, P3PairCosModel.point] using (M.sphereA u).trans eq_comm) 1 (Or.inl rfl)
  have hAm : M.point (-betaA c i j (oth1 i j)) = triplePoint c i j (oth1 i j) (-σ) := by
    simpa only [zero_add, neg_one_mul, mul_neg_one] using
      model_root hc hij hiA hjA M 0 _ σ M.betaA_range.1 M.betaA_range.2 hσ hcross ha'
        (fun u => by simpa only [sub_zero, P3PairCosModel.point] using (M.sphereA u).trans eq_comm) (-1) (Or.inr rfl)
  have hBp : M.point (phiE c i j+betaA c i j (oth2 i j)) = triplePoint c i j (oth2 i j) σ := by
    simpa only [one_mul, mul_one] using
      model_root hc hij hiB hjB M _ _ σ M.betaB_range.1 M.betaB_range.2 hσ hcross halignedB
        (fun u => (M.sphereB u).trans eq_comm) 1 (Or.inl rfl)
  have hBm : M.point (phiE c i j-betaA c i j (oth2 i j)) = triplePoint c i j (oth2 i j) (-σ) := by
    simpa only [neg_one_mul, mul_neg_one, ← sub_eq_add_neg] using
      model_root hc hij hiB hjB M _ _ σ M.betaB_range.1 M.betaB_range.2 hσ hcross halignedB
        (fun u => (M.sphereB u).trans eq_comm) (-1) (Or.inr rfl)
  rw [hothers, Finset.sum_pair hAB]
  have heps : (-1 : ℝ) ≠ 1 := by norm_num
  simp only [Finset.sum_pair heps]
  rcases hσ with rfl | rfl
  · simp only [neg_one_mul, one_mul, neg_neg] at hAp hAm hBp hBm ⊢
    rw [← hAp, ← hAm, ← hBp, ← hBm]
    unfold modelFourRoots
    split_ifs <;> ring
  · simp only [neg_one_mul, one_mul, neg_neg] at hAp hAm hBp hBm ⊢
    rw [← hAp, ← hAm, ← hBp, ← hBm]
    unfold modelFourRoots
    split_ifs <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E5.reflected_endpointSum {G : Type*} [AddCommGroup G] (F : ℝ → G)
    (L : List (ℝ × ℝ)) :
    CircleArc.RawPieces.endpointSum (fun t => F (2*Real.pi-t))
      (L.map (fun ab => (2*Real.pi-ab.2, 2*Real.pi-ab.1))) =
      -CircleArc.RawPieces.endpointSum F L := by
  have he (t : ℝ) : 2*Real.pi-(2*Real.pi-t) = t := by ring
  induction L with
  | nil => simp [CircleArc.RawPieces.endpointSum]
  | cons ab L ih =>
      simp only [CircleArc.RawPieces.endpointSum, List.map_cons, List.sum_cons,
        Prod.fst, Prod.snd, he] at ih ⊢
      rw [ih]
      abel
end
section
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore.E5
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem HardSphereB5.Lean.Geometry.PathCore.pair_endpoint_sum_signed_roots (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0)
    {i j : Fin 4} (hij : i≠j) (D : PairArcDecomposition c i j) :
    (D.intervals.map (fun ab => inner ℝ (cross (c i) (c j)) (D.point ab.2-D.point ab.1))).sum =
      ∑ k ∈ (Finset.univ.erase i).erase j, ∑ ε ∈ ({-1,1} : Finset ℝ),
        if triplePoint c i j k ε ∈ Kset c then
          ε*inner ℝ (cross (c i) (c j)) (triplePoint c i j k ε) else 0 := by
  obtain ⟨M, hA, hB⟩ := aligned_model_exists hc i j hij
  let a := betaA c i j (oth1 i j)
  let b := betaA c i j (oth2 i j)
  let φ := phiE c i j
  let n := (1/dist (c i) (c j)) • (c j-c i)
  have hn : ‖n‖ = 1 := by
    dsimp [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr M.dist_pos),
      ← dist_eq_norm, dist_comm (c j) (c i), one_div_mul_cancel M.dist_pos.ne']
  have hp : ∀ k, inner ℝ n (M.e k) = 0 := by
    intro k
    simp only [n, real_inner_smul_left, M.perp k, mul_zero]
  have hnorm : ‖-(M.e 0)‖ = 1 := by simp [M.ortho.1 0]
  have hperp : inner ℝ (-(M.e 0)) (c j-c i) = 0 := by
    rw [inner_neg_left, real_inner_comm]; simp [M.perp 0]
  have hneg : cross n (-(M.e 0)) = -(cross n (M.e 0)) := by
    ext k; fin_cases k <;> simp [cross, SphereGeom.cross, cross_apply] <;> ring
  let A : P9IntervalData (fun t => M.point (t-Real.pi)) (Kset c) :=
    ⟨CircleArc.RawPieces.intervals a b φ,
      CircleArc.RawPieces.bounds a b φ M.betaA_range.1 M.betaA_range.2
        M.betaB_range.1 M.betaB_range.2 M.phi_range.1 M.phi_range.2,
      CircleArc.RawPieces.disjoint a b φ M.betaB_range.2,
      canonical_cover hc hP i j hij M⟩
  let F : ℝ → ℝ := fun t => inner ℝ (cross (c i) (c j)) (M.point (t-Real.pi))
  rcases P9_cross_orientation n M.e M.ortho hn hp with hcros | hcros
  · have hchart (t : ℝ) :
        (1/2:ℝ) • (c i+c j) + Real.sqrt (1-q c i j/4) •
          (Real.cos t • (-(M.e 0)) + Real.sin t • cross n (-(M.e 0))) = M.point (t-Real.pi) := by
      rw [hneg, hcros]
      simp [P3PairCosModel.point, SphereGeom.circlePt, Real.cos_sub, Real.sin_sub]
    let E : PairArcDecomposition c i j :=
      ⟨-(M.e 0), hnorm, hperp, A.intervals, A.bounds, A.disjoint,
        fun t ht => by rw [hchart]; exact A.cover t ht⟩
    have hE (t : ℝ) : E.point t = M.point (t-Real.pi) := hchart t
    calc
      _ = (E.intervals.map (fun ab => inner ℝ (cross (c i) (c j)) (E.point ab.2-E.point ab.1))).sum :=
        pair_endpointSum_eq_of_decomposition hc i j hij D E
      _ = modelFourRoots M := by
        simp only [hE, inner_sub_right]
        exact model_endpoint_sum hc hP hij M
      _ = _ := by
        simpa only [one_mul] using
          model_four_roots_signed hc hij M 1 (Or.inl rfl) (by simpa [n] using hcros) hA hB
  · have hchart (t : ℝ) :
        (1/2:ℝ) • (c i+c j) + Real.sqrt (1-q c i j/4) •
          (Real.cos t • (-(M.e 0)) + Real.sin t • cross n (-(M.e 0))) =
          M.point (2*Real.pi-t-Real.pi) := by
      rw [hneg, hcros]
      have he : 2*Real.pi-t-Real.pi = Real.pi-t := by ring
      rw [he]
      simp [P3PairCosModel.point, SphereGeom.circlePt, Real.cos_sub, Real.sin_sub]
    let B := A.reflect
    let E : PairArcDecomposition c i j :=
      ⟨-(M.e 0), hnorm, hperp, B.intervals, B.bounds, B.disjoint,
        fun t ht => by rw [hchart]; exact B.cover t ht⟩
    have hE (t : ℝ) : E.point t = M.point (2*Real.pi-t-Real.pi) := hchart t
    calc
      _ = (E.intervals.map (fun ab => inner ℝ (cross (c i) (c j)) (E.point ab.2-E.point ab.1))).sum :=
        pair_endpointSum_eq_of_decomposition hc i j hij D E
      _ = -modelFourRoots M := by
        simp only [hE, inner_sub_right]
        change CircleArc.RawPieces.endpointSum (fun t => F (2*Real.pi-t))
          (A.intervals.map (fun ab => (2*Real.pi-ab.2, 2*Real.pi-ab.1))) = -modelFourRoots M
        rw [reflected_endpointSum]
        exact congrArg Neg.neg (model_endpoint_sum hc hP hij M)
      _ = _ := by
        simpa only [neg_one_mul] using
          model_four_roots_signed hc hij M (-1) (Or.inr rfl) (by simpa [n] using hcros) hA hB
end
noncomputable section
open MeasureTheory Real
section
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace Classical
end
section
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000
private def HardSphereB5.Lean.Geometry.PathCore.E2.faceDelta (v w : Pt) : ℝ := DeltaT (sq v) (sq w) (sq (v - w))
private def HardSphereB5.Lean.Geometry.PathCore.E2.faceQ (v w : Pt) : ℝ := QT (sq v) (sq w) (sq (v - w))
private def HardSphereB5.Lean.Geometry.PathCore.E2.center (v w : Pt) : Pt :=
  (sq w * (sq v - sq w + sq (v - w)) / faceDelta v w) • v +
  (sq v * (sq w - sq v + sq (v - w)) / faceDelta v w) • w
private def HardSphereB5.Lean.Geometry.PathCore.E2.height (v w : Pt) : ℝ := Real.sqrt (faceQ v w / faceDelta v w)
private def HardSphereB5.Lean.Geometry.PathCore.E2.orientedNormal (v w z : Pt) : Pt :=
  if 0 < ⟪z, cross v w⟫ then ‖cross v w‖⁻¹ • cross v w
  else -(‖cross v w‖⁻¹ • cross v w)
private def HardSphereB5.Lean.Geometry.PathCore.E2.triple (v w : Pt) : Set Pt := {x | ‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1}
private def HardSphereB5.Lean.Geometry.PathCore.E2.fourthThreshold (v w z : Pt) : ℝ :=
  (sq z - 2 * ⟪z, center v w⟫) / (2 * ⟪z, orientedNormal v w z⟫)
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.sq_sub (x y : Pt) : sq (x - y) = sq x + sq y - 2 * ⟪x, y⟫ := by
  simp only [sq, inner_sub_left, inner_sub_right, real_inner_comm y x]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.sq_eq_one_iff (x : Pt) : sq x = 1 ↔ ‖x‖ = 1 := by
  rw [sq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg x]
  · intro h; rw [h]; norm_num
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.cross_v (v w : Pt) : ⟪v, cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.cross_w (v w : Pt) : ⟪w, cross v w⟫ = 0 := by
  rw [inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.cross_sq (v w : Pt) :
    sq (cross v w) = sq v * sq w - ⟪v, w⟫ ^ 2 := by
  simp only [sq, inner_coords, cross_coords]
  simp
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.gram_resolution (v w x : Pt) :
    (sq v * sq w - ⟪v, w⟫ ^ 2) • x =
      (sq w * ⟪v, x⟫ - ⟪v, w⟫ * ⟪w, x⟫) • v +
      (sq v * ⟪w, x⟫ - ⟪v, w⟫ * ⟪v, x⟫) • w +
      ⟪cross v w, x⟫ • cross v w := by
  simp only [sq, inner_coords]
  ext i
  fin_cases i <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.delta_gram (v w : Pt) :
    faceDelta v w = 4 * (sq v * sq w - ⟪v, w⟫ ^ 2) := by
  simp only [faceDelta, DeltaT, sq_sub]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.q_delta (v w : Pt) :
    faceQ v w = faceDelta v w - sq v * sq w * sq (v - w) := rfl
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.center_inner_v (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, v⟫ = sq v / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq, real_inner_comm w v]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.center_inner_w (v w : Pt) (hD : faceDelta v w ≠ 0) :
    ⟪center v w, w⟫ = sq w / 2 := by
  simp only [center, inner_add_left, real_inner_smul_left]
  field_simp [hD]
  rw [delta_gram, sq_sub]
  simp only [sq]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.center_sq (v w : Pt) (hD : faceDelta v w ≠ 0) :
    sq (center v w) = sq v * sq w * sq (v - w) / faceDelta v w := by
  change ⟪center v w, center v w⟫ = _
  nth_rw 2 [center]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    center_inner_v v w hD, center_inner_w v w hD]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.cross_norm_pos (v w : Pt) (hD : 0 < faceDelta v w) : 0 < ‖cross v w‖ := by
  have he := delta_gram v w
  have hs := cross_sq v w
  rw [sq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cross v w)]
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.unit_cross_norm (v w : Pt) (hD : 0 < faceDelta v w) :
    ‖‖cross v w‖⁻¹ • cross v w‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cross_norm_pos v w hD))]
  exact inv_mul_cancel₀ (ne_of_gt (cross_norm_pos v w hD))
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.normal_norm (v w z : Pt) (hD : 0 < faceDelta v w) :
    ‖orientedNormal v w z‖ = 1 := by
  unfold orientedNormal
  split_ifs <;> simp only [norm_neg, unit_cross_norm v w hD]
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.normal_sq (v w z : Pt) (hD : 0 < faceDelta v w) :
    sq (orientedNormal v w z) = 1 := by
  rw [sq_eq_norm_sq, normal_norm v w z hD]; norm_num
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.normal_v (v w z : Pt) : ⟪v, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_v]
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.normal_w (v w z : Pt) : ⟪w, orientedNormal v w z⟫ = 0 := by
  unfold orientedNormal
  split_ifs <;> simp [real_inner_smul_right, cross_w]
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.normal_oriented (v w z : Pt) (hD : 0 < faceDelta v w)
    (hG : ⟪z, cross v w⟫ ≠ 0) : 0 < ⟪z, orientedNormal v w z⟫ := by
  have hi := inv_pos.mpr (cross_norm_pos v w hD)
  unfold orientedNormal
  split_ifs with hz
  · rw [real_inner_smul_right]; exact mul_pos hi hz
  · rw [inner_neg_right, real_inner_smul_right]
    have hz' : ⟪z, cross v w⟫ < 0 := lt_of_le_of_ne (le_of_not_gt hz) hG
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hi hz')
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.center_normal (v w z : Pt) : ⟪center v w, orientedNormal v w z⟫ = 0 := by
  simp only [center, inner_add_left, real_inner_smul_left, normal_v, normal_w,
    mul_zero, add_zero]
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.perp_as_normal (v w z d : Pt) (hD : 0 < faceDelta v w)
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
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.height_pos (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    0 < height v w := Real.sqrt_pos.mpr (div_pos hQ hD)
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.center_height (v w : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
    sq (center v w) + height v w ^ 2 = 1 := by
  rw [center_sq v w (ne_of_gt hD)]
  unfold height
  rw [Real.sq_sqrt (le_of_lt (div_pos hQ hD)), q_delta]
  field_simp [ne_of_gt hD]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.mem_triple_iff (v w x : Pt) :
    x ∈ triple v w ↔ sq x = 1 ∧ ⟪x, v⟫ = sq v / 2 ∧ ⟪x, w⟫ = sq w / 2 := by
  change (‖x‖ = 1 ∧ ‖x - v‖ = 1 ∧ ‖x - w‖ = 1) ↔ _
  simp only [← sq_eq_one_iff, sq_sub]
  constructor
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, hv, hw⟩; exact ⟨hx, by linarith, by linarith⟩
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.center_line_sq (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w) :
    sq (center v w + r • orientedNormal v w z) = sq (center v w) + r ^ 2 := by
  have ho := center_normal v w z
  have hn : ⟪orientedNormal v w z, orientedNormal v w z⟫ = 1 := normal_sq v w z hD
  have ho' : ⟪orientedNormal v w z, center v w⟫ = 0 := (real_inner_comm (center v w) _).trans ho
  simp only [sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ho, ho', hn]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.line_mem_triple (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
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
private theorem HardSphereB5.Lean.Geometry.PathCore.E2.triple_exact (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
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
private lemma HardSphereB5.Lean.Geometry.PathCore.E2.triple_points_ne (v w z : Pt) (hD : 0 < faceDelta v w) (hQ : 0 < faceQ v w) :
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
private theorem HardSphereB5.Lean.Geometry.PathCore.E2.fourth_sq_formula (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hr : r ^ 2 = height v w ^ 2) :
    ‖center v w + r • orientedNormal v w z - z‖ ^ 2 - 1 =
      sq z - 2 * ⟪z, center v w⟫ - 2 * r * ⟪z, orientedNormal v w z⟫ := by
  rw [← sq_eq_norm_sq, sq_sub, center_line_sq v w z r hD,
    inner_add_left, real_inner_smul_left, real_inner_comm z (center v w),
    real_inner_comm z (orientedNormal v w z), hr]
  linarith [center_height v w hD hQ]
private theorem HardSphereB5.Lean.Geometry.PathCore.E2.fourth_mem_iff (v w z : Pt) (r : ℝ) (hD : 0 < faceDelta v w)
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
private theorem HardSphereB5.Lean.Geometry.PathCore.E2.oriented_triple_bridge (v w z : Pt) (hD : 0 < faceDelta v w)
    (hQ : 0 < faceQ v w) (hG : ⟪z, cross v w⟫ ≠ 0) :
    ‖orientedNormal v w z‖ = 1 ∧
      ⟪v, orientedNormal v w z⟫ = 0 ∧ ⟪w, orientedNormal v w z⟫ = 0 ∧
      0 < ⟪z, orientedNormal v w z⟫ ∧
      triple v w = {center v w + height v w • orientedNormal v w z,
        center v w - height v w • orientedNormal v w z} :=
  ⟨normal_norm v w z hD, normal_v v w z, normal_w v w z,
    normal_oriented v w z hD hG, triple_exact v w z hD hQ⟩
end
end
section
open HardSphereB5.Lean (Pt)
private lemma HardSphereB5.Lean.Geometry.PathCore.cayley_menger_face_identity (X Y s : ℝ) (l : Fin 4) :
    Apoly X Y s l ^ 2 - 4 * Hpoly X Y s * Qpoly X Y s l =
      -Dpoly X Y s l * P4poly X Y s := by
  fin_cases l <;> simp [Apoly, Hpoly, Qpoly, Dpoly, DeltaT, P4poly] <;> ring
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
end
section
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
end
section
open HardSphereB5.Lean (Pt)
open scoped RealInnerProductSpace
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
      E2.triple (c (faceVerts l).2.1 - c (faceVerts l).1)
        (c (faceVerts l).2.2 - c (faceVerts l).1)} := by
  ext x
  fin_cases l <;>
    simp [triplePts, faceVerts, Fin.forall_fin_succ, E2.triple,
      dist_eq_norm, norm_sub_base] <;> tauto
private lemma HardSphereB5.Lean.Geometry.PathCore.TG_sq_q (c : Fin 4 → Pt) (i j : Fin 4) : E2.sq (c j-c i) = q c i j := by
  exact (q_inner c i j).symm
private lemma HardSphereB5.Lean.Geometry.PathCore.TG_sq_diff_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    E2.sq ((c j-c i)-(c k-c i)) = q c j k := by
  have he : (c j-c i)-(c k-c i) = c j-c k := by abel
  rw [he, TG_sq_q, q_symm']
private lemma HardSphereB5.Lean.Geometry.PathCore.face_TG_D (c : Fin 4 → Pt) (l : Fin 4) :
    E2.faceDelta (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) =
    Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 := by
  simp only [E2.faceDelta, TG_sq_q, TG_sq_diff_q, Deltaf]
private lemma HardSphereB5.Lean.Geometry.PathCore.face_TG_Q (c : Fin 4 → Pt) (l : Fin 4) :
    E2.faceQ (c (faceVerts l).2.1-c (faceVerts l).1)
      (c (faceVerts l).2.2-c (faceVerts l).1) = Qface c l := by
  simp only [E2.faceQ, TG_sq_q, TG_sq_diff_q, Qface, Qf]
private lemma HardSphereB5.Lean.Geometry.PathCore.normal_projection_identity (v w z : Pt) (hD : 0 < E2.faceDelta v w) :
    E2.faceDelta v w * (inner ℝ z (E2.orientedNormal v w z))^2 =
      4 * (inner ℝ z (cross v w))^2 := by
  have hn := ne_of_gt (E2.cross_norm_pos v w hD)
  have hd : E2.faceDelta v w = 4*‖cross v w‖^2 := by
    rw [E2.delta_gram, ← E2.cross_sq, E2.sq_eq_norm_sq]
  rw [hd]
  unfold E2.orientedNormal
  split_ifs <;> simp only [inner_neg_right, real_inner_smul_right]
  all_goals field_simp [hn]
  all_goals ring
private lemma HardSphereB5.Lean.Geometry.PathCore.numerator_identity (v w z : Pt) (hD : E2.faceDelta v w ≠ 0) :
    E2.faceDelta v w * (E2.sq z - 2*inner ℝ z (E2.center v w)) =
      faceAPoly (E2.sq v) (E2.sq w) (E2.sq (v-w))
        (E2.sq z) (E2.sq (z-v)) (E2.sq (z-w)) := by
  simp only [E2.center, inner_add_right, real_inner_smul_right, faceAPoly]
  have hd : DeltaT (E2.sq v) (E2.sq w)
      (E2.sq (v-w)) = E2.faceDelta v w := rfl
  rw [hd]
  simp only [E2.sq_sub]
  field_simp [hD]
  rw [E2.delta_gram]
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
  let D := E2.faceDelta v w
  let Q := E2.faceQ v w
  let N := E2.orientedNormal v w z
  let h := E2.height v w
  let o := E2.center v w
  let p := c i + (o+h•N)
  let m := c i + (o-h•N)
  let a := E2.sq z - 2*inner ℝ z o
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
  have hn : 0 < inner ℝ z N := E2.normal_oriented v w z hD hG
  have hh : 0 < h := E2.height_pos v w hD hQ
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hh) hn
  have hpm : p ≠ m := by
    exact fun he => E2.triple_points_ne v w z hD hQ (add_left_cancel he)
  have htr : triplePts c l = {p,m} := by
    rw [triplePts_translate c l]
    change {x | x-c i ∈ E2.triple v w} = {p,m}
    rw [E2.triple_exact v w z hD hQ]
    ext x
    simp [p,m,o,h,N,Set.mem_insert_iff,Set.mem_singleton_iff,sub_eq_iff_eq_add,add_comm]
  have hp : (dist p (c l))^2-1 = a-b := by
    have he : p-c l = o+h•N-z := by dsimp [p,z]; abel
    rw [dist_eq_norm,he]
    exact E2.fourth_sq_formula v w z h hD hQ rfl
  have hm : (dist m (c l))^2-1 = a+b := by
    have he : m-c l = o+(-h)•N-z := by dsimp [m,z]; simp only [neg_smul]; abel
    rw [dist_eq_norm,he,E2.fourth_sq_formula v w z (-h) hD hQ (neg_sq h)]
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
end
section
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore.E6
open scoped Classical
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.q_symm (c : Fin 4 → Pt) (i j : Fin 4) : q c j i = q c i j := by
  simp only [q, dist_comm]
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.D_swap (c : Fin 4 → Pt) (i j k : Fin 4) : Deltaf c i k j = Deltaf c i j k := by
  simp only [Deltaf, DeltaT, q_symm c j k]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.D_cycle (c : Fin 4 → Pt) (i j k : Fin 4) : Deltaf c j k i = Deltaf c i j k := by
  simp only [Deltaf, DeltaT, q_symm c i j, q_symm c i k]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.Q_swap (c : Fin 4 → Pt) (i j k : Fin 4) : Qf c i k j = Qf c i j k := by
  simp only [Qf, QT, DeltaT, q_symm c j k]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.Q_cycle (c : Fin 4 → Pt) (i j k : Fin 4) : Qf c j k i = Qf c i j k := by
  simp only [Qf, QT, DeltaT, q_symm c i j, q_symm c i k]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.cross_swap (v w : Pt) : cross w v = -cross v w := by
  ext n
  fin_cases n <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.cross_cycle (p q r : Pt) : cross (r-q) (p-q) = cross (q-p) (r-p) := by
  ext n
  fin_cases n <;> simp [cross_coords] <;> ring
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.triple_swap (c : Fin 4 → Pt) (i j k : Fin 4) (ε : ℝ) :
    triplePoint c i k j ε = triplePoint c i j k (-ε) := by
  simp only [triplePoint, faceCircRel, D_swap c i j k, Q_swap c i j k, q_symm c j k, cross_swap (c j-c i) (c k-c i)]
  module
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.triple_cycle (c : Fin 4 → Pt) (i j k : Fin 4)
    (hd : Deltaf c i j k ≠ 0) (ε : ℝ) :
    triplePoint c j k i ε = triplePoint c i j k ε := by
  simp only [triplePoint, faceCircRel, D_cycle c i j k, Q_cycle c i j k, q_symm c i j,
    q_symm c i k, cross_cycle (c i) (c j) (c k)]
  have hc : c j +
      (q c i j * (q c j k-q c i j+q c i k) / Deltaf c i j k) • (c k-c j) +
      (q c j k * (q c i j-q c j k+q c i k) / Deltaf c i j k) • (c i-c j) =
    c i + (q c i k * (q c i j-q c i k+q c j k) / Deltaf c i j k) • (c j-c i) +
      (q c i j * (q c i k-q c i j+q c j k) / Deltaf c i j k) • (c k-c i) := by
    ext n
    change c j n +
      (q c i j*(q c j k-q c i j+q c i k)/Deltaf c i j k)*(c k n-c j n) +
      (q c j k*(q c i j-q c j k+q c i k)/Deltaf c i j k)*(c i n-c j n) =
      c i n + (q c i k*(q c i j-q c i k+q c j k)/Deltaf c i j k)*(c j n-c i n) +
      (q c i j*(q c i k-q c i j+q c j k)/Deltaf c i j k)*(c k n-c i n)
    field_simp [hd]
    simp only [Deltaf, DeltaT]
    ring
  convert congrArg (fun x : Pt => x + (ε*2*√(Qf c i j k)/Deltaf c i j k) •
    cross (c j-c i) (c k-c i)) hc using 1 <;> abel
end
section
open HardSphereB5.Lean (Pt)
open scoped Classical
private theorem HardSphereB5.Lean.Geometry.PathCore.E4.canonical_retained_iff {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (l : Fin 4)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
    triplePoint c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 ε ∈ Kset c ↔
      if 0 < P4poly X Y s then ε = Real.sign
        (det3 (c (faceVerts l).2.1-c (faceVerts l).1)
          (c (faceVerts l).2.2-c (faceVerts l).1) (c l-c (faceVerts l).1))
      else Apoly X Y s l < 0 := by
  classical
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  let D := Deltaf c i j k
  let Q := Qface c l
  let z := det3 (c j-c i) (c k-c i) (c l-c i)
  let a := q c i l-2*inner ℝ (c l-c i) (faceCircRel c i j k)
  let b := 4*√Q/D*|z|
  let bs := 4*√Q/D*z
  have hij : i≠j := by dsimp [i,j]; fin_cases l <;> decide
  have hik : i≠k := by dsimp [i,k]; fin_cases l <;> decide
  have hjk : j≠k := by dsimp [j,k]; fin_cases l <;> decide
  have hil : i≠l := by dsimp [i]; fin_cases l <;> decide
  have hjl : j≠l := by dsimp [j]; fin_cases l <;> decide
  have hkl : k≠l := by dsimp [k]; fin_cases l <;> decide
  have hD : 0 < D := (tetrahedron_metric hc).2.2.2.1 i j k hij hik hjk
  have hQ : 0 < Q := by
    change 0 < Qface c l
    rw [(face_polys c X Y s hc l).1]
    exact path_Qpoly_pos c X Y s hc l
  have hzsq : 4*z^2 = Hpoly X Y s := by
    have h := gram_from_q c i j k l
    rw [(face_polys c X Y s hc l).2.2.2] at h
    exact h
  have hz : z ≠ 0 := by intro he; rw [he] at hzsq; nlinarith [hc.H_pos]
  have hb : 0 < b := mul_pos (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hQ)) hD)
    (abs_pos.2 hz)
  have ha : D*a = Apoly X Y s l := Aface_eq_poly hc l
  have hb2 : D^2*b^2 = 4*Hpoly X Y s*Q := by
    dsimp [b]
    field_simp [hD.ne']
    nlinarith [Real.sq_sqrt hQ.le, sq_abs z]
  have hdisc : (Apoly X Y s l)^2-4*Hpoly X Y s*Q = -D*P4poly X Y s :=
    face_circumradius_certificate hc l
  have hm := margin_selector (Hpoly X Y s) D Q (P4poly X Y s)
    (Apoly X Y s l) a b hc.H_pos hD hQ hb ha hb2 hdisc
  have hret : triplePoint c i j k ε ∈ Kset c ↔ a-ε*bs ≤ 0 := by
    have hunit := (face_circumcenter_identities hc i j k hij hik hjk).2.2.2 ε hε
    have hmem : ∀ m : Fin 4, m≠l → m ∈ ({i,j,k} : Finset (Fin 4)) := by
      dsimp [i,j,k]
      fin_cases l <;> decide
    have hsq := triple_retention_test hc i j k l hij hik hil hjk hjl hkl ε hε
    have hsq' : dist (triplePoint c i j k ε) (c l)^2-1 = a-ε*bs := by
      calc
        _ = a-ε*4*√Q/D*z := hsq
        _ = a-ε*bs := by dsimp [bs]; ring
    have hle : dist (triplePoint c i j k ε) (c l) ≤ 1 ↔ a-ε*bs ≤ 0 := by
      constructor <;> intro h <;> nlinarith [hsq', (dist_nonneg : 0 ≤ dist (triplePoint c i j k ε) (c l))]
    rw [← hle]
    simp only [Kset, body, Set.mem_iInter, Finset.mem_univ, true_implies, Metric.mem_closedBall]
    constructor
    · intro h
      simpa only [dist_comm] using h l
    · intro h m
      by_cases he : m=l
      · simpa [he,dist_comm] using h
      · exact le_of_eq (hunit m (hmem m he))
  change triplePoint c i j k ε ∈ Kset c ↔
    if 0 < P4poly X Y s then ε=Real.sign z else Apoly X Y s l<0
  rw [hret]
  by_cases hbulk : 0<P4poly X Y s
  · rw [if_pos hbulk]
    have hab := hm.1 hbulk
    rcases lt_trichotomy z 0 with hn | he | hp
    · have hbs : bs = -b := by dsimp [bs,b]; rw [abs_of_neg hn]; ring
      rw [hbs, Real.sign_of_neg hn]
      rcases hε with rfl | rfl <;> norm_num <;> nlinarith
    · exact (hz he).elim
    · have hbs : bs = b := by dsimp [bs,b]; rw [abs_of_pos hp]
      rw [hbs, Real.sign_of_pos hp]
      rcases hε with rfl | rfl <;> norm_num <;> nlinarith
  · rw [if_neg hbulk]
    have hsliv : P4poly X Y s<0 := lt_of_le_of_ne (le_of_not_gt hbulk) hP
    have hba := hm.2.1 hsliv
    rw [← hm.2.2]
    rcases lt_trichotomy z 0 with hn | he | hp
    · have hbs : bs = -b := by dsimp [bs,b]; rw [abs_of_neg hn]; ring
      rw [hbs]
      rcases hε with rfl | rfl <;> constructor <;> intro h <;> nlinarith
    · exact (hz he).elim
    · have hbs : bs = b := by dsimp [bs,b]; rw [abs_of_pos hp]
      rw [hbs]
      rcases hε with rfl | rfl <;> constructor <;> intro h <;> nlinarith
end
section
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore.E6
open scoped Classical
private def HardSphereB5.Lean.Geometry.PathCore.E4.faceRoot (c : Fin 4 → Pt) (l : Fin 4) : ℝ :=
  ∑ ε ∈ ({-1,1} : Finset ℝ), if
    triplePoint c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 ε ∈ Kset c then
    ε * inner ℝ
      (cross (c (faceVerts l).1) (c (faceVerts l).2.1) +
       cross (c (faceVerts l).2.1) (c (faceVerts l).2.2) +
       cross (c (faceVerts l).2.2) (c (faceVerts l).1))
      (triplePoint c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 ε) else 0
private theorem HardSphereB5.Lean.Geometry.PathCore.E4.faceRoot_eq {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (l : Fin 4) :
    faceRoot c l = (nRet c l : ℝ)*√(Qface c l)/2 +
      if 0<P4poly X Y s then
        Real.sign (det3 (c (faceVerts l).2.1-c (faceVerts l).1)
          (c (faceVerts l).2.2-c (faceVerts l).1) (c l-c (faceVerts l).1)) *
        inner ℝ (cross (c (faceVerts l).2.1-c (faceVerts l).1)
          (c (faceVerts l).2.2-c (faceVerts l).1)) (c (faceVerts l).1) else 0 := by
  classical
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  have hij : i≠j := by dsimp [i,j]; fin_cases l <;> decide
  have hik : i≠k := by dsimp [i,k]; fin_cases l <;> decide
  have hjk : j≠k := by dsimp [j,k]; fin_cases l <;> decide
  have hp := triple_signed_contribution hc i j k hij hik hjk 1 (Or.inl rfl)
  have hm := triple_signed_contribution hc i j k hij hik hjk (-1) (Or.inr rfl)
  simp only [faceRoot, Finset.sum_insert (by norm_num : (-1:ℝ) ∉ ({1} : Finset ℝ)),
    Finset.sum_singleton]
  change (if triplePoint c i j k (-1) ∈ Kset c then (-1)*inner ℝ
    (cross (c i) (c j)+cross (c j) (c k)+cross (c k) (c i))
      (triplePoint c i j k (-1)) else 0) +
    (if triplePoint c i j k 1 ∈ Kset c then 1*inner ℝ
    (cross (c i) (c j)+cross (c j) (c k)+cross (c k) (c i))
      (triplePoint c i j k 1) else 0) = _
  rw [hp,hm,canonical_retained_iff hc hP l (-1) (Or.inr rfl),
    canonical_retained_iff hc hP l 1 (Or.inl rfl),nRet_coordinate_selector c X Y s hc hP l]
  by_cases hb : 0<P4poly X Y s
  · simp only [hb, if_true, Nat.cast_one]
    have hz : det3 (c j-c i) (c k-c i) (c l-c i) ≠ 0 := by
      have h := face_det_pos c X Y s hc l
      intro he
      change 0 < (det3 (c j-c i) (c k-c i) (c l-c i))^2 at h
      rw [he] at h
      norm_num at h
    rcases lt_trichotomy (det3 (c j-c i) (c k-c i) (c l-c i)) 0 with hn | he | hpos
    · rw [Real.sign_of_neg hn]
      norm_num [Qface,i,j,k] <;> ring
    · exact (hz he).elim
    · rw [Real.sign_of_pos hpos]
      norm_num [Qface,i,j,k] <;> ring
  · simp only [hb, if_false]
    by_cases hA : Apoly X Y s l<0 <;> simp [hA,Qface,i,j,k] <;> ring
private theorem HardSphereB5.Lean.Geometry.PathCore.E4.faceRoot_contraction {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) :
    (∑ l : Fin 4, faceRoot c l) =
      ((∑ l : Fin 4, (nRet c l : ℝ)*√(Qface c l)) -
        if 0<P4poly X Y s then √(Hpoly X Y s) else 0)/2 := by
  simp_rw [faceRoot_eq hc hP]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_div]
  by_cases hb : 0<P4poly X Y s
  · simp only [hb,if_true]
    rw [face_signed_planes_path hc]
    ring
  · simp [hb]
end
section
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore.E6
open scoped Classical
private def HardSphereB5.Lean.Geometry.PathCore.E4.rootTerm (c : Fin 4 → Pt) (i j k : Fin 4) : ℝ :=
  ∑ ε ∈ ({-1,1} : Finset ℝ), if triplePoint c i j k ε ∈ Kset c then
    ε*inner ℝ (cross (c i) (c j)) (triplePoint c i j k ε) else 0
private def HardSphereB5.Lean.Geometry.PathCore.E4.signedTripleSum (c : Fin 4 → Pt) : ℝ :=
  ∑ e : PairIndex, ∑ k ∈ (Finset.univ.erase e.1.1).erase e.1.2, rootTerm c e.1.1 e.1.2 k
private theorem HardSphereB5.Lean.Geometry.PathCore.E4.triangle_root_terms (c : Fin 4 → Pt) (i j k : Fin 4)
    (hd : Deltaf c i j k ≠ 0) :
    rootTerm c i j k + rootTerm c i k j + rootTerm c j k i =
    ∑ ε ∈ ({-1,1} : Finset ℝ), if triplePoint c i j k ε ∈ Kset c then
      ε*inner ℝ (cross (c i) (c j)+cross (c j) (c k)+cross (c k) (c i))
        (triplePoint c i j k ε) else 0 := by
  classical
  simp only [rootTerm, Finset.sum_insert (by norm_num : (-1:ℝ) ∉ ({1} : Finset ℝ)),
    Finset.sum_singleton]
  rw [triple_swap c i j k (-1), triple_swap c i j k 1,
    triple_cycle c i j k hd (-1), triple_cycle c i j k hd 1]
  simp only [neg_neg, cross_swap (c i) (c k), inner_add_left, inner_neg_left]
  split_ifs <;> ring
private def HardSphereB5.Lean.Geometry.PathCore.E4.pairUniv : Finset PairIndex :=
  {⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(0,3),by decide⟩,
    ⟨(1,2),by decide⟩,⟨(1,3),by decide⟩,⟨(2,3),by decide⟩}
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.pairUniv_eq : (Finset.univ : Finset PairIndex) = pairUniv := by
  ext e
  rcases e with ⟨⟨i,j⟩,h⟩
  fin_cases i <;> fin_cases j <;> simp_all [pairUniv] <;> norm_num [Fin.lt_def] at h
private lemma HardSphereB5.Lean.Geometry.PathCore.E4.two_remaining_sum (c : Fin 4 → Pt) (i j : Fin 4) :
    (∑ k ∈ (Finset.univ.erase i).erase j, rootTerm c i j k) =
    ∑ k : Fin 4, if k ≠ i ∧ k ≠ j then rootTerm c i j k else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_filter, true_and]
  tauto
private theorem HardSphereB5.Lean.Geometry.PathCore.E4.signedTripleSum_eq_faces {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) :
    signedTripleSum c = ∑ l : Fin 4, faceRoot c l := by
  have h012 : Deltaf c 0 1 2 ≠ 0 :=
    ((tetrahedron_metric hc).2.2.2.1 0 1 2 (by decide) (by decide) (by decide)).ne'
  have h013 : Deltaf c 0 1 3 ≠ 0 :=
    ((tetrahedron_metric hc).2.2.2.1 0 1 3 (by decide) (by decide) (by decide)).ne'
  have h023 : Deltaf c 0 2 3 ≠ 0 :=
    ((tetrahedron_metric hc).2.2.2.1 0 2 3 (by decide) (by decide) (by decide)).ne'
  have h123 : Deltaf c 1 2 3 ≠ 0 :=
    ((tetrahedron_metric hc).2.2.2.1 1 2 3 (by decide) (by decide) (by decide)).ne'
  have f012 := triangle_root_terms c 0 1 2 h012
  have f013 := triangle_root_terms c 0 1 3 h013
  have f023 := triangle_root_terms c 0 2 3 h023
  have f123 := triangle_root_terms c 1 2 3 h123
  change rootTerm c 0 1 2 + rootTerm c 0 2 1 + rootTerm c 1 2 0 = faceRoot c 3 at f012
  change rootTerm c 0 1 3 + rootTerm c 0 3 1 + rootTerm c 1 3 0 = faceRoot c 2 at f013
  change rootTerm c 0 2 3 + rootTerm c 0 3 2 + rootTerm c 2 3 0 = faceRoot c 1 at f023
  change rootTerm c 1 2 3 + rootTerm c 1 3 2 + rootTerm c 2 3 1 = faceRoot c 0 at f123
  unfold signedTripleSum
  rw [pairUniv_eq]
  simp only [pairUniv, Finset.sum_insert, Finset.sum_singleton]
  simp [two_remaining_sum, Fin.sum_univ_four]
  linarith only [f012,f013,f023,f123]
end
section
open HardSphereB5.Lean (Pt)
open scoped Classical
private theorem HardSphereB5.Lean.Geometry.PathCore.signed_triple_sum_contraction {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) :
    (∑ e : PairIndex, ∑ k ∈ (Finset.univ.erase e.1.1).erase e.1.2,
      ∑ ε ∈ ({-1,1} : Finset ℝ), if triplePoint c e.1.1 e.1.2 k ε ∈ Kset c then
        ε*inner ℝ (cross (c e.1.1) (c e.1.2)) (triplePoint c e.1.1 e.1.2 k ε) else 0) =
    ((∑ l : Fin 4, (nRet c l : ℝ)*√(Qface c l)) -
      if 0<P4poly X Y s then √(Hpoly X Y s) else 0)/2 := by
  change E4.signedTripleSum c = _
  rw [E4.signedTripleSum_eq_faces hc]
  exact E4.faceRoot_contraction hc hP
end
open MeasureTheory Real
open HardSphereB5.Lean (Pt)
open HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ}
set_option maxHeartbeats 4000000 in
theorem proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_contraction (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0)
  (D : ∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2) :
  rawEndpointSum c D = ((∑ l, (nRet c l : ℝ)*√(Qface c l)) -
    (if 0<P4poly X Y s then √(Hpoly X Y s) else 0)) / 2 := by
  rw [← HardSphereB5.Lean.Geometry.PathCore.signed_triple_sum_contraction hc hP]
  unfold HardSphereB5.Lean.Geometry.PathCore.rawEndpointSum
  apply Finset.sum_congr rfl
  intro e he
  exact HardSphereB5.Lean.Geometry.PathCore.pair_endpoint_sum_signed_roots hc hP e.2.ne (D e)
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_contraction
