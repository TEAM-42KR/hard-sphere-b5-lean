import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 1200000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_representative_geometry (v : ℝ × ℝ × ℝ) (hv : v ∈ Dfull) :
  pRep v.1 ∈ FA ∧ pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2) ∈ FB ∧
  0 < v.2.2 ∧ dist (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) = √v.2.2 := by
  rcases hv with ⟨hX0, hX1, hY0, hY1, hHpos⟩
  have hXrad : 0 < v.1 * (1 - v.1 / 4) := mul_pos hX0 (by linarith)
  have hYrad : 0 < v.2.1 * (1 - v.2.1 / 4) := mul_pos hY0 (by linarith)
  have hXsq := Real.sq_sqrt hXrad.le
  have hYsq := Real.sq_sqrt hYrad.le
  have hb : 0 < b0 v.1 v.2.1 := by
    dsimp only [b0]
    positivity
  have hb2 : (b0 v.1 v.2.1)^2 =
      4 * (v.1 * (1-v.1/4)) * (v.2.1 * (1-v.2.1/4)) := by
    dsimp only [b0]
    rw [mul_pow, mul_pow, hXsq, hYsq]
    ring
  have hH : Hpoly v.1 v.2.1 v.2.2 =
      (b0 v.1 v.2.1)^2 - (a0 v.1 v.2.1-v.2.2)^2 := by
    rw [hb2]
    dsimp only [Hpoly, a0]
    ring
  have htlo : -1 < (a0 v.1 v.2.1-v.2.2) / b0 v.1 v.2.1 := by
    apply (lt_div_iff₀ hb).2
    rw [hH] at hHpos
    nlinarith [sq_nonneg (b0 v.1 v.2.1 + (a0 v.1 v.2.1-v.2.2))]
  have hthi : (a0 v.1 v.2.1-v.2.2) / b0 v.1 v.2.1 < 1 := by
    apply (div_lt_iff₀ hb).2
    rw [hH] at hHpos
    nlinarith [sq_nonneg (b0 v.1 v.2.1 - (a0 v.1 v.2.1-v.2.2))]
  have hcos : Real.cos (chiPlus v.1 v.2.1 v.2.2) =
      (a0 v.1 v.2.1-v.2.2) / b0 v.1 v.2.1 :=
    Real.cos_arccos htlo.le hthi.le
  have hmulcos : b0 v.1 v.2.1 * Real.cos (chiPlus v.1 v.2.1 v.2.2) =
      a0 v.1 v.2.1-v.2.2 := by rw [hcos]; field_simp [hb.ne']
  have htrig := Real.sin_sq_add_cos_sq (chiPlus v.1 v.2.1 v.2.2)
  have hp : ‖pRep v.1‖^2 = 1 := by
    simp [pRep, e1, HardSphereB5.Lean.e, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_succ, EuclideanSpace.single_apply]
    nlinarith [hXsq]
  have hpe : dist (pRep v.1) e ^2 = v.1 := by
    rw [dist_eq_norm]
    simp [pRep, e1, HardSphereB5.Lean.e, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_succ, EuclideanSpace.single_apply]
    nlinarith [hXsq]
  have hp'e : dist (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) e ^2 = 1 := by
    rw [dist_eq_norm]
    simp [pRep2, e1, e2, HardSphereB5.Lean.e, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_succ, EuclideanSpace.single_apply, mul_pow]
    nlinarith [hYsq, htrig]
  have hp' : ‖pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)‖^2 = v.2.1 := by
    simp [pRep2, e1, e2, HardSphereB5.Lean.e, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_succ, EuclideanSpace.single_apply, mul_pow]
    nlinarith [hYsq, htrig]
  have hdist : dist (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) ^2 = v.2.2 := by
    rw [dist_eq_norm]
    simp [pRep, pRep2, e1, e2, HardSphereB5.Lean.e, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_succ, EuclideanSpace.single_apply]
    dsimp only [b0, a0] at hmulcos
    nlinarith [hXsq, hYsq, htrig]
  have hsin : 0 < Real.sin (chiPlus v.1 v.2.1 v.2.2) :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hthi) (Real.arccos_lt_pi.mpr htlo)
  have hne : pRep v.1 ≠ pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2) := by
    intro heq
    have hc := congrArg (fun p : Pt => p 2) heq
    simp [pRep, pRep2, e1, e2, HardSphereB5.Lean.e, EuclideanSpace.single_apply] at hc
    rcases hc with hc | hc
    · exact (Real.sqrt_pos.2 hYrad).ne' hc
    · exact hsin.ne' hc
  have hs : 0 < v.2.2 := by rw [← hdist]; exact sq_pos_of_pos (dist_pos.mpr hne)
  refine ⟨?_, ?_, hs, ?_⟩
  · change dist (pRep v.1) 0 = 1 ∧ dist (pRep v.1) e ≤ 1
    rw [dist_zero_right]
    constructor
    · nlinarith [norm_nonneg (pRep v.1)]
    · nlinarith [dist_nonneg (x := pRep v.1) (y := e)]
  · change dist (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) e = 1 ∧
      dist (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) 0 ≤ 1
    rw [dist_zero_right]
    constructor
    · nlinarith [dist_nonneg (x := pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) (y := e)]
    · nlinarith [norm_nonneg (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2))]
  · calc
      _ = √(dist (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2))^2) :=
        (Real.sqrt_sq dist_nonneg).symm
      _ = √v.2.2 := congrArg Real.sqrt hdist
