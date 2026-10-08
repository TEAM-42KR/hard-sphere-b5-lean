import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore SphereGeom
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000
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

theorem proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_unrestricted_false :
    ∃ x : Fin 3 → Pt, (∀ i j, i ≠ j → dist (x i) (x j) ^ 2 = 7 / 2) ∧
      QT (7 / 2) (7 / 2) (7 / 2) ≤ 0 ∧ (⋂ i, Metric.closedBall (x i) 1) = ∅ ∧
      0 < (volume (Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1)).toReal := by
  refine ⟨eqTri, eqTri_dist_sq, ?_, eqTri_empty, eqTri_pair_pos⟩
  norm_num [QT, DeltaT]
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_unrestricted_false
