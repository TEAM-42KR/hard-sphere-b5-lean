import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import Mathlib
import HardSphereB5Lean.Theorems.Thm_SolidGeom_volume_lens_closed
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open HardSphereB5.Lean.Geometry.PathCore HardSphereB5.Lean MeasureTheory Real
open scoped Classical

noncomputable section
open MeasureTheory Real

open HardSphereB5.Lean (Pt)
open scoped Classical

open HardSphereB5.Lean (Pt)
set_option maxHeartbeats 1200000

private lemma fallback_obtuse (a b c : ℝ) (hb0 : 0 < b) (hc0 : 0 < c)
    (hb : b ≤ 1) (hc : c ≤ 1) (hba : b ≤ a) (hca : c ≤ a) (hQ : QT a b c ≤ 0) :
    b + c < a := by
  by_contra hh
  have habc : a ≤ b + c := le_of_not_gt hh
  have ha2 : a ≤ 2 := by linarith
  have hfirst : 0 < b*c*(3-a) := mul_pos (mul_pos hb0 hc0) (by linarith)
  have hsecond : 0 ≤ (b+c-a)*((a-c)+(a-b)) := mul_nonneg (by linarith) (by linarith)
  have hthird : 0 ≤ (a-c)*(a-b) := mul_nonneg (by linarith) (by linarith)
  have hidentity : QT a b c = b*c*(3-a)+(b+c-a)*((a-c)+(a-b))+(a-c)*(a-b) := by
    unfold QT DeltaT
    ring
  linarith only [hQ, hfirst, hsecond, hthird, hidentity]

private lemma distance_square (y A B : Pt) :
    dist y A ^ 2 = inner ℝ (y-B) (y-B) - 2*inner ℝ (y-B) (A-B) + inner ℝ (A-B) (A-B) := by
  rw [dist_eq_norm]
  have he : y-A = (y-B)-(A-B) := by abel
  rw [he, norm_sub_sq_real]
  simp only [real_inner_self_eq_norm_sq]

private lemma fallback_lens_subset (A B C : Pt)
    (ha0 : 0 < dist B C ^ 2) (ha4 : dist B C ^ 2 < 4)
    (hba : dist B A ^ 2 ≤ dist B C ^ 2) (hca : dist C A ^ 2 ≤ dist B C ^ 2)
    (hobt : dist B A ^ 2 + dist C A ^ 2 < dist B C ^ 2)
    (hQ : QT (dist B C ^ 2) (dist B A ^ 2) (dist C A ^ 2) ≤ 0) :
    Metric.closedBall B 1 ∩ Metric.closedBall C 1 ⊆ Metric.closedBall A 1 := by
  intro y hy
  let a := dist B C ^ 2
  let b := dist B A ^ 2
  let c := dist C A ^ 2
  let u := C-B
  let v := A-B
  let t := y-B
  let p := inner ℝ u v
  let lam := p/a
  let n := v-lam • u
  let z := t-(1/2 : ℝ) • u
  let k := a-b-c
  have haa : 0 < a := ha0
  have hk : 0 < k := by dsimp [k,a,b,c]; linarith [hobt]
  have hbnon : 0 ≤ b := sq_nonneg _
  have hcnon : 0 ≤ c := sq_nonneg _
  have huu : inner ℝ u u = a := by simp [u, a, real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  have hvv : inner ℝ v v = b := by simp [v, b, real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  have hvc : inner ℝ (v-u) (v-u) = c := by
    have he : v-u = A-C := by dsimp [u,v]; abel
    simp [he, c, real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  have hvu : inner ℝ v u = p := by simpa only [p] using (real_inner_comm u v)
  have hpc : c = a+b-2*p := by
    simp only [inner_sub_left, inner_sub_right, hvu, huu, hvv] at hvc
    change b-p-(p-a) = c at hvc
    linarith only [hvc]
  have hlam : a*lam = p := by dsimp [lam]; field_simp
  have hp0 : 0 ≤ p := by change c ≤ a at hca; linarith only [hpc,hca,hbnon]
  have hpa : p ≤ a := by change b ≤ a at hba; linarith only [hpc,hba,hcnon]
  have hlam0 : 0 ≤ lam := div_nonneg hp0 haa.le
  have hlam1 : lam ≤ 1 := by
    change p/a ≤ 1
    apply (div_le_iff₀ haa).mpr
    simpa only [one_mul] using hpa
  have hun : inner ℝ u n = 0 := by
    dsimp [n]
    simp only [inner_sub_right, real_inner_smul_right]
    rw [huu]
    change p-lam*a = 0
    linarith only [hlam]
  have hnn : a*inner ℝ n n = a*b-p^2 := by
    dsimp [n]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,huu,hvv,hvu]
    change a*(b-lam*p-(lam*p-lam*(lam*a))) = a*b-p^2
    linear_combination (a*lam-p)*hlam
  have hnormn0 : 0 ≤ inner ℝ n n := real_inner_self_nonneg
  have hprod : 0 ≤ a*(k^2-16*(1-a/4)*inner ℝ n n) := by
    have hid : a*(k^2-16*(1-a/4)*inner ℝ n n) = -4*QT a b c := by
      dsimp [k]
      rw [hpc]
      unfold QT DeltaT
      linear_combination (4*a-16)*hnn
    rw [hid]
    dsimp [a,b,c]
    linarith only [hQ]
  have hbound : 16*(1-a/4)*inner ℝ n n ≤ k^2 := by
    have := nonneg_of_mul_nonneg_right hprod haa
    linarith only [this]
  have hB : inner ℝ t t ≤ 1 := by
    have hd := Metric.mem_closedBall.mp hy.1
    have : dist y B ^ 2 ≤ 1 := by nlinarith only [hd, dist_nonneg (x := y) (y := B)]
    simpa [t, real_inner_self_eq_norm_sq, dist_eq_norm] using this
  have hC : inner ℝ t t -2*inner ℝ t u+a ≤ 1 := by
    have hd := Metric.mem_closedBall.mp hy.2
    have : dist y C ^ 2 ≤ 1 := by nlinarith only [hd, dist_nonneg (x := y) (y := C)]
    rw [distance_square y C B] at this
    change inner ℝ t t-2*inner ℝ t u+inner ℝ u u ≤ 1 at this
    simpa only [huu] using this
  have hzz : inner ℝ z z ≤ 1-a/4 := by
    dsimp [z]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,real_inner_comm u t]
    rw [huu]
    rw [real_inner_comm t u]
    change inner ℝ t t - (1/2)*inner ℝ t u - ((1/2)*inner ℝ t u-(1/2)*((1/2)*a)) ≤ 1-a/4
    linarith only [hB,hC]
  have hzn : inner ℝ z n = inner ℝ t n := by
    dsimp [z]
    simp only [inner_sub_left,real_inner_smul_left]
    rw [hun]
    ring
  have hcs := real_inner_mul_inner_self_le z n
  have hmul := mul_le_mul_of_nonneg_right hzz hnormn0
  have hisq : (4*inner ℝ t n)^2 ≤ k^2 := by rw [hzn] at hcs; nlinarith only [hcs,hmul,hbound]
  have hiabs : |4*inner ℝ t n| ≤ k := (sq_le_sq₀ (abs_nonneg _) hk.le).mp (by simpa only [sq_abs] using hisq)
  have hi : -2*inner ℝ t n ≤ k/2 := by linarith only [hiabs,neg_le_abs (4*inner ℝ t n)]
  have hweighted : inner ℝ t t-2*lam*inner ℝ t u+lam*a ≤ 1 := by
    have h1 := mul_nonneg (sub_nonneg.mpr hlam1) (sub_nonneg.mpr hB)
    have h2 := mul_nonneg hlam0 (sub_nonneg.mpr hC)
    nlinarith only [h1,h2]
  have htn : inner ℝ t n = inner ℝ t v-lam*inner ℝ t u := by
    dsimp [n]
    simp only [inner_sub_right,real_inner_smul_right]
  have hyA : dist y A ^ 2 ≤ 1 := by
    rw [distance_square y A B]
    change inner ℝ t t-2*inner ℝ t v+inner ℝ v v ≤ 1
    rw [hvv]
    dsimp [k] at hi
    rw [htn] at hi
    nlinarith only [hlam,hpc,hweighted,hi]
  apply Metric.mem_closedBall.mpr
  nlinarith only [hyA,dist_nonneg (x := y) (y := A)]

private theorem pair_replacement_body_s5proof (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
 (ha4 : dist (x 1) (x 2)^2<4) (hb : dist (x 0) (x 1)^2≤1) (hcc : dist (x 0) (x 2)^2≤1)
 (hlong : dist (x 0) (x 1)^2≤dist (x 1) (x 2)^2 ∧ dist (x 0) (x 2)^2≤dist (x 1) (x 2)^2)
 (hQ : QT (dist (x 1) (x 2)^2) (dist (x 1) (x 0)^2) (dist (x 2) (x 0)^2)≤0) :
 (⋂ i, Metric.closedBall (x i) 1)=Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1 := by
  have h12 : x 1 ≠ x 2 := hnd.injective.ne (by decide)
  have h10 : x 1 ≠ x 0 := hnd.injective.ne (by decide)
  have h20 : x 2 ≠ x 0 := hnd.injective.ne (by decide)
  have ha0 : 0 < dist (x 1) (x 2)^2 := sq_pos_of_pos (dist_pos.mpr h12)
  have hb0 : 0 < dist (x 1) (x 0)^2 := sq_pos_of_pos (dist_pos.mpr h10)
  have hc0 : 0 < dist (x 2) (x 0)^2 := sq_pos_of_pos (dist_pos.mpr h20)
  rw [dist_comm (x 0) (x 1)] at hb hlong
  rw [dist_comm (x 0) (x 2)] at hcc hlong
  have hobt := fallback_obtuse _ _ _ hb0 hc0 hb hcc hlong.1 hlong.2 hQ
  have hsub := fallback_lens_subset (x 0) (x 1) (x 2) ha0 ha4 hlong.1 hlong.2 hobt hQ
  have he : (⋂ i, Metric.closedBall (x i) 1) = Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1 := by
    ext y
    simp only [Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨h 1,h 2⟩
    · intro h i
      fin_cases i
      · exact hsub h
      · exact h.1
      · exact h.2
  exact he

private theorem pair_replacement_conditional (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
    (ha4 : dist (x 1) (x 2) ^ 2 < 4) (hb : dist (x 0) (x 1) ^ 2 ≤ 1) (hcc : dist (x 0) (x 2) ^ 2 ≤ 1)
    (hlong : dist (x 0) (x 1) ^ 2 ≤ dist (x 1) (x 2) ^ 2 ∧ dist (x 0) (x 2) ^ 2 ≤ dist (x 1) (x 2) ^ 2)
    (hQ : QT (dist (x 1) (x 2) ^ 2) (dist (x 1) (x 0) ^ 2) (dist (x 2) (x 0) ^ 2) ≤ 0) :
    (volume (⋂ i, Metric.closedBall (x i) 1)).toReal = V2 (dist (x 1) (x 2)) := by
  rw [pair_replacement_body_s5proof x hnd ha4 hb hcc hlong hQ]
  have hd : dist (x 1) (x 2) ≤ 2 := by
    nlinarith only [ha4, dist_nonneg (x := x 1) (y := x 2)]
  exact SolidGeom.volume_lens_closed _ _ hd

private def eqTri : Fin 3 → Pt :=
  ![WithLp.toLp 2 ![Real.sqrt (7/6), 0, 0],
    WithLp.toLp 2 ![-Real.sqrt (7/6)/2, Real.sqrt (7/8), 0],
    WithLp.toLp 2 ![-Real.sqrt (7/6)/2, -Real.sqrt (7/8), 0]]

private lemma dist_sq_coords (u v : Pt) :
    dist u v ^ 2 = (u 0 - v 0)^2 + (u 1 - v 1)^2 + (u 2 - v 2)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ, Real.dist_eq, sq_abs, add_assoc]

private lemma eqTri_dist_sq (i j : Fin 3) (hij : i ≠ j) :
    dist (eqTri i) (eqTri j) ^ 2 = 7/2 := by
  have hr : Real.sqrt (7/6) ^ 2 = 7/6 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt (7/8) ^ 2 = 7/8 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;>
    simp_all [dist_sq_coords, eqTri, WithLp.toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> nlinarith

private lemma eqTri_empty : (⋂ i, Metric.closedBall (eqTri i) 1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have h (i : Fin 3) : dist y (eqTri i) ≤ 1 := Metric.mem_closedBall.mp (Set.mem_iInter.mp hy i)
  have hsq (i : Fin 3) : dist y (eqTri i)^2 ≤ 1 := by
    nlinarith [h i, dist_nonneg (x := y) (y := eqTri i)]
  have h0 := hsq 0
  have h1 := hsq 1
  have h2 := hsq 2
  have hr : Real.sqrt (7/6) ^ 2 = 7/6 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt (7/8) ^ 2 = 7/8 := Real.sq_sqrt (by norm_num)
  simp only [dist_sq_coords] at h0 h1 h2
  simp only [eqTri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, WithLp.ofLp_toLp, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  simp only [sub_zero, sub_neg_eq_add, zero_sub, neg_zero] at h0 h1 h2
  nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]

private lemma eqTri_pair_pos :
    0 < (volume (Metric.closedBall (eqTri 1) 1 ∩ Metric.closedBall (eqTri 2) 1)).toReal := by
  let m : Pt := WithLp.toLp 2 ![-Real.sqrt (7/6)/2, 0, 0]
  have hs : Real.sqrt (7/8) ^ 2 = 7/8 := Real.sq_sqrt (by norm_num)
  have hm1 : dist m (eqTri 1) < 1 := by
    have hh : dist m (eqTri 1)^2 = 7/8 := by
      simp only [dist_sq_coords, m, eqTri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, WithLp.ofLp_toLp, Matrix.head_cons, Matrix.tail_cons, sub_self, zero_sub, sub_zero, neg_sq, neg_neg, zero_pow, zero_add, add_zero]
      nlinarith [hs]
    nlinarith [dist_nonneg (x := m) (y := eqTri 1)]
  have hm2 : dist m (eqTri 2) < 1 := by
    have hh : dist m (eqTri 2)^2 = 7/8 := by
      simp only [dist_sq_coords, m, eqTri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, WithLp.ofLp_toLp, Matrix.head_cons, Matrix.tail_cons, sub_self, zero_sub, sub_zero, neg_sq, neg_neg, zero_pow, zero_add, add_zero]
      nlinarith [hs]
    nlinarith [dist_nonneg (x := m) (y := eqTri 2)]
  have hp : 0 < volume (Metric.closedBall (eqTri 1) 1 ∩ Metric.closedBall (eqTri 2) 1) := by
    apply Measure.measure_pos_of_nonempty_interior
    rw [interior_inter]
    exact ⟨m, Metric.ball_subset_interior_closedBall hm1, Metric.ball_subset_interior_closedBall hm2⟩
  exact ENNReal.toReal_pos hp.ne' (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_closedBall_lt_top).ne

private theorem pair_replacement_unrestricted_false :
    ∃ x : Fin 3 → Pt, (∀ i j, i ≠ j → dist (x i) (x j) ^ 2 = 7 / 2) ∧
      (⋂ i, Metric.closedBall (x i) 1) = ∅ ∧
      0 < (volume (Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1)).toReal := by
  exact ⟨eqTri, eqTri_dist_sq, eqTri_empty, eqTri_pair_pos⟩

open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_body : ∀ (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
 (ha4 : dist (x 1) (x 2)^2<4) (hb : dist (x 0) (x 1)^2≤1) (hcc : dist (x 0) (x 2)^2≤1)
 (hlong : dist (x 0) (x 1)^2≤dist (x 1) (x 2)^2 ∧ dist (x 0) (x 2)^2≤dist (x 1) (x 2)^2)
 (hQ : QT (dist (x 1) (x 2)^2) (dist (x 1) (x 0)^2) (dist (x 2) (x 0)^2)≤0),
  (⋂ i, Metric.closedBall (x i) 1)=Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1 := by
  exact @pair_replacement_body_s5proof
