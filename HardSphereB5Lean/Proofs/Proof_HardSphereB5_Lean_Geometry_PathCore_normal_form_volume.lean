import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_threeBallVolume
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_volume
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_volume
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_table
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_pair_width
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_no_sliver_at_s_one
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_no_near_sliver_on_diagonal
set_option autoImplicit false

noncomputable section
open MeasureTheory Real
private abbrev HardSphereB5.Lean.Geometry.PathCore.s5c_scope_anchor_normal_form_volume : Unit := ()
section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_sum4 {A : Type*} [AddCommMonoid A] (f : Fin 4 → A) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  rw [hu]
  simp [add_assoc]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_qsymm (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_Q_swap12 (c : Fin 4 → Pt) (i j k : Fin 4) :
    Qf c j i k = Qf c i j k := by
  simp only [Qf, p8_qsymm c j i]
  unfold QT DeltaT
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_Q_swap23 (c : Fin 4 → Pt) (i j k : Fin 4) :
    Qf c i k j = Qf c i j k := by
  simp only [Qf, p8_qsymm c k j]
  unfold QT DeltaT
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_Q_rot (c : Fin 4 → Pt) (i j k : Fin 4) :
    Qf c k i j = Qf c i j k := by
  rw [p8_Q_swap12, p8_Q_swap23]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_beta_symm (c : Fin 4 → Pt) (i j k : Fin 4) :
    betaA c j i k = betaA c i j k := by
  simp only [betaA, p8_Q_swap12, p8_qsymm c j i]
  congr 2 <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_gamma_symm (c : Fin 4 → Pt) (i j k : Fin 4) :
    gammaA c i k j = gammaA c i j k := by
  simp only [gammaA, p8_Q_swap23, p8_qsymm c k j]
  congr 2 <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_sqrt_q (c : Fin 4 → Pt) (i j : Fin 4) :
    Real.sqrt (q c i j) = dist (c i) (c j) := by
  exact Real.sqrt_sq (dist_nonneg (x := c i) (y := c j))

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_triangle_volume (hc : IsPathConfig c X Y s) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    vol c {i,j,k} = 2*Real.pi - (2/3) *
      (gammaA c i j k + gammaA c j i k + gammaA c k i j) -
      (g (dist (c i) (c j)) * betaA c i j k +
        g (dist (c i) (c k)) * betaA c i k j +
        g (dist (c j) (c k)) * betaA c j k i) + Real.sqrt (Qf c i j k)/6 := by
  have hv := HardSphereB5.Lean.Geometry.threeBallVolume c X Y s
    hc.q01 hc.q02 hc.q03 hc.q12 hc.q13 hc.q23 hc.X_pos hc.X_lt_one
    hc.Y_pos hc.Y_lt_one hc.H_pos i j k hij hik hjk
  have hbody : body c {i,j,k} = Metric.closedBall (c i) 1 ∩
      Metric.closedBall (c j) 1 ∩ Metric.closedBall (c k) 1 := by
    ext x
    simp only [body, Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton,
      Set.mem_inter_iff]
    constructor
    · intro hx
      exact ⟨⟨hx i (Or.inl rfl), hx j (Or.inr (Or.inl rfl))⟩,
        hx k (Or.inr (Or.inr rfl))⟩
    · rintro ⟨⟨hi, hj⟩, hk⟩ n (rfl | rfl | rfl)
      · exact hi
      · exact hj
      · exact hk

  rw [vol, hbody]
  convert hv using 1
  simp only [gammaA, betaA, g, atan2, p8_Q_swap12, p8_Q_swap23, p8_Q_rot,
    p8_qsymm c j i, p8_qsymm c k i, p8_qsymm c k j]
  unfold Qf QT DeltaT q
  simp only [Real.sqrt_sq (dist_nonneg (x := c i) (y := c j)),
    Real.sqrt_sq (dist_nonneg (x := c i) (y := c k)),
    Real.sqrt_sq (dist_nonneg (x := c j) (y := c k))]
  try ring

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private def HardSphereB5.Lean.Geometry.PathCore.p8_volume_rhs (c : Fin 4 → Pt) (X Y s : ℝ) : ℝ :=
  8 * Real.pi / 3 - (1 / 3) * ∑ l, (nRet c l : ℝ) * sigmaF c l
      - (1 / 2) * ∑ i, ∑ j, (if i < j then g (dist (c i) (c j)) * ell c i j else 0)
      + (1 / 12) * ∑ l, (nRet c l : ℝ) * Real.sqrt (Qface c l)
      - (if 0 < P4poly X Y s then Real.sqrt (Hpoly X Y s) / 12 else 0)

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_volume_bulk_of_deps
    (hc : IsPathConfig c X Y s) (hb : 0 < P4poly X Y s) :
    vol c Finset.univ = p8_volume_rhs c X Y s := by
  have hn := (bulk_incidence hc hb).1
  have t012 := p8_triangle_volume hc 0 1 2 (by decide) (by decide) (by decide)
  have t013 := p8_triangle_volume hc 0 1 3 (by decide) (by decide) (by decide)
  have t023 := p8_triangle_volume hc 0 2 3 (by decide) (by decide) (by decide)
  have t123 := p8_triangle_volume hc 1 2 3 (by decide) (by decide) (by decide)
  have f0 : faceSet (0:Fin 4) = {1, 2, 3} := by decide
  have f1 : faceSet (1:Fin 4) = {0, 2, 3} := by decide
  have f2 : faceSet (2:Fin 4) = {0, 1, 3} := by decide
  have f3 : faceSet (3:Fin 4) = {0, 1, 2} := by decide
  have w01 := pair_width hc (ne_of_gt hb) 0 1 (by decide)
  simp only [hn, Nat.cast_one, one_mul, hb, if_true, not_lt_of_ge hb.le, false_and, if_false, sub_zero] at w01
  norm_num [oth1, oth2, Fin.ext_iff] at w01
  have w02 := pair_width hc (ne_of_gt hb) 0 2 (by decide)
  simp only [hn, Nat.cast_one, one_mul, hb, if_true, not_lt_of_ge hb.le, false_and, if_false, sub_zero] at w02
  norm_num [oth1, oth2, Fin.ext_iff] at w02
  have w03 := pair_width hc (ne_of_gt hb) 0 3 (by decide)
  simp only [hn, Nat.cast_one, one_mul, hb, if_true, not_lt_of_ge hb.le, false_and, if_false, sub_zero] at w03
  norm_num [oth1, oth2, Fin.ext_iff] at w03
  have w12 := pair_width hc (ne_of_gt hb) 1 2 (by decide)
  simp only [hn, Nat.cast_one, one_mul, hb, if_true, not_lt_of_ge hb.le, false_and, if_false, sub_zero] at w12
  norm_num [oth1, oth2, Fin.ext_iff] at w12
  have w13 := pair_width hc (ne_of_gt hb) 1 3 (by decide)
  simp only [hn, Nat.cast_one, one_mul, hb, if_true, not_lt_of_ge hb.le, false_and, if_false, sub_zero] at w13
  norm_num [oth1, oth2, Fin.ext_iff] at w13
  have w23 := pair_width hc (ne_of_gt hb) 2 3 (by decide)
  simp only [hn, Nat.cast_one, one_mul, hb, if_true, not_lt_of_ge hb.le, false_and, if_false, sub_zero] at w23
  norm_num [oth1, oth2, Fin.ext_iff] at w23
  rw [HardSphereB5.Lean.Geometry.PathCore.bulk_volume hc hb]
  unfold p8_volume_rhs
  simp only [p8_sum4, hn, Nat.cast_one, one_mul, hb, if_true]
  norm_num only at ⊢
  simp only [f0, f1, f2, f3, t012, t013, t023, t123,
    w01, w02, w03, w12, w13, w23]
  norm_num [sigmaF, Qface, faceVerts, Fin.lt_def, Fin.ext_iff]
  all_goals
    clear hn t012 t013 t023 t123 f0 f1 f2 f3 w01 w02 w03 w12 w13 w23 hc
    apply sub_eq_zero.mp
    ring_nf
    try simp
    change gammaA c 0 1 3 * (-1/3) + gammaA c 1 0 3 * (-1/3) +
      gammaA c 3 0 1 * (-1/3) + Real.sqrt (Qf c 0 1 3) * (12:ℝ)⁻¹ +
      gammaA c 0 1 2 * (-1/3) + gammaA c 1 0 2 * (-1/3) +
      gammaA c 2 0 1 * (-1/3) + Real.sqrt (Qf c 0 1 2) * (12:ℝ)⁻¹ +
      gammaA c 0 1 3 * (3:ℝ)⁻¹ + gammaA c 1 0 3 * (3:ℝ)⁻¹ + gammaA c 3 0 1 * (3:ℝ)⁻¹ +
      gammaA c 0 1 2 * (3:ℝ)⁻¹ + gammaA c 1 0 2 * (3:ℝ)⁻¹ + gammaA c 2 0 1 * (3:ℝ)⁻¹ +
      Real.sqrt (Qf c 0 1 3) * (-1/12) + Real.sqrt (Qf c 0 1 2) * (-1/12) = 0
    ring

end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_V2_g (d : ℝ) : V2 d = 4*Real.pi/3 - Real.pi * g d := by
  unfold V2 g
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_volume_sliver_nearA_of_deps (hc : IsPathConfig c X Y s)
    (hp : P4poly X Y s < 0)
    (hs : s < 1) (hYX : Y < X) : vol c Finset.univ = p8_volume_rhs c X Y s := by
  have ht := (sliver_table hc hp).1 hs hYX
  have n3 : nRet c 3 = 2 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.1) ht.1
  have n2 : nRet c 2 = 0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.1) ht.1
  have n1 : nRet c 1 = 2 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.1) ht.1
  have n0 : nRet c 0 = 0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.2) ht.1
  have t012 := p8_triangle_volume hc 0 1 2 (by decide) (by decide) (by decide)
  have t013 := p8_triangle_volume hc 0 1 3 (by decide) (by decide) (by decide)
  have t023 := p8_triangle_volume hc 0 2 3 (by decide) (by decide) (by decide)
  have t123 := p8_triangle_volume hc 1 2 3 (by decide) (by decide) (by decide)
  have f0 : ({0, 2, oth1 0 2} : Finset (Fin 4)) = {0, 1, 2} := by decide
  have f1 : ({0, 2, oth2 0 2} : Finset (Fin 4)) = {0, 2, 3} := by decide
  have w01 := pair_width hc (ne_of_lt hp) 0 1 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w01
  have w02 := pair_width hc (ne_of_lt hp) 0 2 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w02
  have w03 := pair_width hc (ne_of_lt hp) 0 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w03
  have w12 := pair_width hc (ne_of_lt hp) 1 2 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w12
  have w13 := pair_width hc (ne_of_lt hp) 1 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w13
  have w23 := pair_width hc (ne_of_lt hp) 2 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w23
  rw [sliver_volume hc hp 0 2 (by decide) ht.2]
  unfold p8_volume_rhs
  simp only [p8_sum4, not_lt_of_ge hp.le, if_false]
  norm_num only at ⊢
  simp only [f0, f1, t012, t013, t023, t123, p8_V2_g,
    w01, w02, w03, w12, w13, w23]
  norm_num [n0,n1,n2,n3, sigmaF, Qface, faceVerts, Fin.lt_def, Fin.ext_iff]
  all_goals
    apply sub_eq_zero.mp
    ring_nf
    try simp
    try ring
private lemma HardSphereB5.Lean.Geometry.PathCore.p8_volume_sliver_nearB_of_deps (hc : IsPathConfig c X Y s)
    (hp : P4poly X Y s < 0)
    (hs : s < 1) (hXY : X < Y) : vol c Finset.univ = p8_volume_rhs c X Y s := by
  have ht := (sliver_table hc hp).2.1 hs hXY
  have n3 : nRet c 3 = 0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.1) ht.1
  have n2 : nRet c 2 = 2 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.1) ht.1
  have n1 : nRet c 1 = 0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.1) ht.1
  have n0 : nRet c 0 = 2 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.2) ht.1
  have t012 := p8_triangle_volume hc 0 1 2 (by decide) (by decide) (by decide)
  have t013 := p8_triangle_volume hc 0 1 3 (by decide) (by decide) (by decide)
  have t023 := p8_triangle_volume hc 0 2 3 (by decide) (by decide) (by decide)
  have t123 := p8_triangle_volume hc 1 2 3 (by decide) (by decide) (by decide)
  have f0 : ({1, 3, oth1 1 3} : Finset (Fin 4)) = {0, 1, 3} := by decide
  have f1 : ({1, 3, oth2 1 3} : Finset (Fin 4)) = {1, 2, 3} := by decide
  have w01 := pair_width hc (ne_of_lt hp) 0 1 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w01
  have w02 := pair_width hc (ne_of_lt hp) 0 2 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w02
  have w03 := pair_width hc (ne_of_lt hp) 0 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w03
  have w12 := pair_width hc (ne_of_lt hp) 1 2 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w12
  have w13 := pair_width hc (ne_of_lt hp) 1 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w13
  have w23 := pair_width hc (ne_of_lt hp) 2 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w23
  rw [sliver_volume hc hp 1 3 (by decide) ht.2]
  unfold p8_volume_rhs
  simp only [p8_sum4, not_lt_of_ge hp.le, if_false]
  norm_num only at ⊢
  simp only [f0, f1, t012, t013, t023, t123, p8_V2_g,
    w01, w02, w03, w12, w13, w23]
  norm_num [n0,n1,n2,n3, sigmaF, Qface, faceVerts, Fin.lt_def, Fin.ext_iff]
  all_goals
    apply sub_eq_zero.mp
    ring_nf
    try simp
    try ring
private lemma HardSphereB5.Lean.Geometry.PathCore.p8_volume_sliver_far_of_deps (hc : IsPathConfig c X Y s)
    (hp : P4poly X Y s < 0)
    (hs : 1 < s) : vol c Finset.univ = p8_volume_rhs c X Y s := by
  have ht := (sliver_table hc hp).2.2 hs
  have n3 : nRet c 3 = 0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.1) ht.1
  have n2 : nRet c 2 = 0 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.1) ht.1
  have n1 : nRet c 1 = 2 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.1) ht.1
  have n0 : nRet c 0 = 2 := congrArg (fun v : ℕ × ℕ × ℕ × ℕ => v.2.2.2) ht.1
  have t012 := p8_triangle_volume hc 0 1 2 (by decide) (by decide) (by decide)
  have t013 := p8_triangle_volume hc 0 1 3 (by decide) (by decide) (by decide)
  have t023 := p8_triangle_volume hc 0 2 3 (by decide) (by decide) (by decide)
  have t123 := p8_triangle_volume hc 1 2 3 (by decide) (by decide) (by decide)
  have f0 : ({2, 3, oth1 2 3} : Finset (Fin 4)) = {0, 2, 3} := by decide
  have f1 : ({2, 3, oth2 2 3} : Finset (Fin 4)) = {1, 2, 3} := by decide
  have w01 := pair_width hc (ne_of_lt hp) 0 1 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w01
  have w02 := pair_width hc (ne_of_lt hp) 0 2 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w02
  have w03 := pair_width hc (ne_of_lt hp) 0 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w03
  have w12 := pair_width hc (ne_of_lt hp) 1 2 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w12
  have w13 := pair_width hc (ne_of_lt hp) 1 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w13
  have w23 := pair_width hc (ne_of_lt hp) 2 3 (by decide)
  norm_num [oth1, oth2, Fin.ext_iff, isCommon, n0,n1,n2,n3, hp, not_lt_of_ge hp.le] at w23
  rw [sliver_volume hc hp 2 3 (by decide) ht.2]
  unfold p8_volume_rhs
  simp only [p8_sum4, not_lt_of_ge hp.le, if_false]
  norm_num only at ⊢
  simp only [f0, f1, t012, t013, t023, t123, p8_V2_g,
    w01, w02, w03, w12, w13, w23]
  norm_num [n0,n1,n2,n3, sigmaF, Qface, faceVerts, Fin.lt_def, Fin.ext_iff]
  all_goals
    apply sub_eq_zero.mp
    ring_nf
    try simp
    try ring
end

section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem HardSphereB5.Lean.Geometry.PathCore.normal_form_volume_of_deps (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) :
    vol c Finset.univ = 8 * Real.pi / 3 - (1 / 3) * ∑ l, (nRet c l : ℝ) * sigmaF c l
      - (1 / 2) * ∑ i, ∑ j, (if i < j then g (dist (c i) (c j)) * ell c i j else 0)
      + (1 / 12) * ∑ l, (nRet c l : ℝ) * Real.sqrt (Qface c l)
      - (if 0 < P4poly X Y s then Real.sqrt (Hpoly X Y s) / 12 else 0) := by
  change vol c Finset.univ = p8_volume_rhs c X Y s
  by_cases hb : 0 < P4poly X Y s
  · exact p8_volume_bulk_of_deps hc hb
  · have hp : P4poly X Y s < 0 := lt_of_le_of_ne (le_of_not_gt hb) hP
    have hsne : s ≠ 1 := by
      intro hs
      have hb1 := no_sliver_at_s_one hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one
      rw [← hs] at hb1
      linarith
    rcases lt_or_gt_of_ne hsne with hs | hs
    · have hxne : X ≠ Y := by
        intro he
        have hbd := no_near_sliver_on_diagonal hc hs he
        linarith
      rcases lt_or_gt_of_ne hxne with hxy | hyx
      · exact p8_volume_sliver_nearB_of_deps hc hp hs hxy
      · exact p8_volume_sliver_nearA_of_deps hc hp hs hyx
    · exact p8_volume_sliver_far_of_deps hc hp hs

theorem proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_volume {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) :
    vol c Finset.univ = 8 * π / 3 - (1 / 3) * ∑ l, (nRet c l : ℝ) * sigmaF c l
      - (1 / 2) * ∑ i, ∑ j, (if i < j then g (dist (c i) (c j)) * ell c i j else 0)
      + (1 / 12) * ∑ l, (nRet c l : ℝ) * √(Qface c l)
      - (if 0 < P4poly X Y s then √(Hpoly X Y s) / 12 else 0) := by
  exact normal_form_volume_of_deps hc hP

end

#print axioms HardSphereB5.Lean.Geometry.PathCore.normal_form_volume_of_deps
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_volume
