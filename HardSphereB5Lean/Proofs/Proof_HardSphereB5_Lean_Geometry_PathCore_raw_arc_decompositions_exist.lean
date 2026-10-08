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
set_option autoImplicit false

noncomputable section
open MeasureTheory Real SphereGeom
open scoped Classical RealInnerProductSpace Topology

set_option maxHeartbeats 1200000

private abbrev HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.s5c_scope_anchor_raw_arc_decompositions_exist : Unit := ()
section
open HardSphereB5.Lean.Geometry.PathCore.TripleGeometry
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq (x : Pt) : ℝ := ⟪x, x⟫

end

section
open HardSphereB5.Lean.Geometry.PathCore.TripleGeometry
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq_eq_norm_sq (x : Pt) : sq x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x

end

section
open HardSphereB5.Lean.Geometry.PathCore.TripleGeometry
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.sq_nonneg (x : Pt) : 0 ≤ sq x := by rw [sq_eq_norm_sq]; positivity

end

section
open HardSphereB5.Lean.Geometry.PathCore.TripleGeometry
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.inner_coords (x y : Pt) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

end

section
open HardSphereB5.Lean.Geometry.PathCore.TripleGeometry
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.TripleGeometry.cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1,
      v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := by
  simp [cross, SphereGeom.cross, cross_apply]

end

section
open HardSphereB5.Lean.Geometry.PathCore.TripleGeometry
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
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

end

private abbrev HardSphereB5.Lean.Geometry.PathCore.s5c_scope_anchor_raw_arc_decompositions_exist : Unit := ()
section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.Dpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![DeltaT X 1 s, DeltaT 1 Y s, DeltaT 1 Y 1, DeltaT 1 1 X]

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.gramPoly (a b cc d e f : ℝ) : ℝ :=
  4*a*b*d + (a+b-cc)*(a+d-e)*(b+d-f)
    - a*(b+d-f)^2 - b*(a+d-e)^2 - d*(a+b-cc)^2

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.faceAPoly (a b cc d e f : ℝ) : ℝ :=
  DeltaT a b cc * d - b*(a-b+cc)*(a+d-e) - a*(b-a+cc)*(b+d-f)

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.cross_gram_identity (v w z : Pt) :
    (inner ℝ (SphereGeom.cross v w) z)^2 =
      inner ℝ v v * inner ℝ w w * inner ℝ z z +
      2 * inner ℝ v w * inner ℝ v z * inner ℝ w z -
      inner ℝ v v * (inner ℝ w z)^2 -
      inner ℝ w w * (inner ℝ v z)^2 -
      inner ℝ z z * (inner ℝ v w)^2 :=
  TripleGeometry.cross_gram_identity v w z

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.near_q_symm (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.near_norm_sub_q (c : Fin 4 → Pt) (i j : Fin 4) :
    ‖c i - c j‖ ^ 2 = q c i j := by
  rw [q, dist_eq_norm]

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_q_symm (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_pair_radius_pos (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j) : 0 < Real.sqrt (1 - q c i j / 4) := by
  apply Real.sqrt_pos.2
  linarith [(p3_q_pos_lt_four hc i j hij).2]

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_indices_cover (i j m : Fin 4) (hij : i ≠ j) :
    m = i ∨ m = j ∨ m = oth1 i j ∨ m = oth2 i j := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all [oth1, oth2]

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_betaA_range (c : Fin 4 → Pt) (i j k : Fin 4)
    (hQ : 0 < Qf c i j k) :
    0 < betaA c i j k ∧ betaA c i j k < Real.pi := by
  apply p3_atan2_range
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hQ)

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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

private abbrev CircleArc.s5c_scope_anchor_raw_arc_decompositions_exist : Unit := ()
section
open CircleArc
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
open CircleArc
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
open CircleArc
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
open CircleArc
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
open CircleArc
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
open CircleArc
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
open CircleArc
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
open CircleArc
open HardSphereB5.Lean (Pt)
private theorem CircleArc.cos_cut_periodic_shift (β θ t : ℝ) (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Real.cos β ≤ Real.cos (t - θ) ↔
      ∃ n : ℤ, t ∈ Set.Icc (θ - β + 2 * Real.pi * n) (θ + β + 2 * Real.pi * n) := by
  rw [cos_cut_periodic β (t - θ) hβ0 hβπ]
  constructor <;> rintro ⟨n, hlo, hhi⟩ <;> refine ⟨n, ?_, ?_⟩ <;> linarith

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open CircleArc
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.point {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : ℝ → Pt :=
  SphereGeom.circlePt ((1/2:ℝ) • (c i+c j)) (M.e 0) (M.e 1) (Real.sqrt (1-q c i j/4))

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.arcA {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : Set Pt :=
  M.point '' Set.Icc (-betaA c i j (oth1 i j)) (betaA c i j (oth1 i j))

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.P3PairCosModel.arcB {c : Fin 4 → Pt} {i j : Fin 4} (M : P3PairCosModel c i j) : Set Pt :=
  M.point '' Set.Icc (phiE c i j-betaA c i j (oth2 i j)) (phiE c i j+betaA c i j (oth2 i j))

end

section
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

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_spheres (c : Fin 4 → Pt) (i j : Fin 4) (M : P3PairCosModel c i j) :
    Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 = M.point '' Set.Icc 0 (2*Real.pi) := by
  exact CircleArc.pair_sphere_chart_two (c i) (c j) M.e M.ortho M.perp M.dist_pos M.dist_lt_two

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private lemma HardSphereB5.Lean.Geometry.PathCore.p3_model_point_on_spheres (c : Fin 4 → Pt) (i j : Fin 4)
    (M : P3PairCosModel c i j) (t : ℝ) :
    M.point t ∈ Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 := by
  exact CircleArc.pair_circle_on_spheres (c i) (c j) M.e M.ortho M.perp M.dist_lt_two t

end

section
open HardSphereB5.Lean.Geometry.PathCore
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
open HardSphereB5.Lean.Geometry.PathCore
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

end
section
open HardSphereB5.Lean.Geometry.PathCore
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

private abbrev CircleArc.RawPieces.s5c_scope_anchor_raw_arc_decompositions_exist : Unit := ()
section
open CircleArc.RawPieces

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
open HardSphereB5.Lean.Geometry.PathCore
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
  simp only [TripleGeometry.inner_coords, TripleGeometry.cross_coords]
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

open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore

theorem proof_HardSphereB5_Lean_Geometry_PathCore_raw_arc_decompositions_exist {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (hP : P4poly X Y s ≠ 0) :
    Nonempty (∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2) := by
  classical
  exact ⟨fun e => Classical.choice (P9_pair_arc_exists hc hP e.1.1 e.1.2 e.2.ne)⟩

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_raw_arc_decompositions_exist
