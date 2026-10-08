import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
open HardSphereB5.Lean (Pt e)
open SphereGeom
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff (p p' D : Pt) (hpp : dist p p' < 2) :
    (dist D p = 1 ∧ dist D p' = 1) ↔
      ∃ q : Pt, ‖q‖ = 1 ∧ inner ℝ q (p' - p) = 0 ∧
        D = midpoint ℝ p p' + Real.sqrt (1 - dist p p' ^ 2 / 4) • q := by
  let r : ℝ := Real.sqrt (1 - dist p p' ^ 2 / 4)
  let m : Pt := midpoint ℝ p p'
  let d : Pt := p' - p
  let w : Pt := (1 / 2 : ℝ) • d
  let v : Pt := D - m
  have hs2 : dist p p' ^ 2 < (2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2 hpp
  have hrad : 0 < 1 - dist p p' ^ 2 / 4 := by nlinarith only [hs2]
  have hr : 0 < r := Real.sqrt_pos.2 hrad
  have hrsq : r ^ 2 = 1 - dist p p' ^ 2 / 4 := Real.sq_sqrt hrad.le
  have hd : ‖d‖ = dist p p' := by
    dsimp [d]
    rw [dist_eq_norm, norm_sub_rev]
  have hw : ‖w‖ = dist p p' / 2 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hd]
    ring
  have hmp : m - p = w := by
    dsimp [m, w, d]
    simpa using (midpoint_sub_left (R := ℝ) p p')
  have hmp' : m - p' = -w := by
    dsimp [m, w, d]
    rw [midpoint_sub_right, ← neg_sub p' p, smul_neg]
    norm_num
  have hDp : D - p = v + w := by
    calc
      D - p = (D - m) + (m - p) := by abel
      _ = v + w := by rw [hmp]
  have hDp' : D - p' = v - w := by
    calc
      D - p' = (D - m) + (m - p') := by abel
      _ = v + -w := by rw [hmp']
      _ = v - w := by abel
  change (dist D p = 1 ∧ dist D p' = 1) ↔
    ∃ q : Pt, ‖q‖ = 1 ∧ inner ℝ q d = 0 ∧ D = m + r • q
  constructor
  · rintro ⟨ha, hb⟩
    have ha' : ‖v + w‖ = 1 := by rw [← hDp, ← dist_eq_norm]; exact ha
    have hb' : ‖v - w‖ = 1 := by rw [← hDp', ← dist_eq_norm]; exact hb
    have haa := norm_add_sq_real v w
    have hbb := norm_sub_sq_real v w
    rw [ha', hw] at haa
    rw [hb', hw] at hbb
    have hvw : inner ℝ v w = 0 := by nlinarith only [haa, hbb]
    have hv_sq : ‖v‖ ^ 2 = r ^ 2 := by nlinarith only [haa, hbb, hrsq]
    have hvnorm : ‖v‖ = r := by nlinarith only [hv_sq, norm_nonneg v, hr]
    have hvd : inner ℝ v d = 0 := by
      dsimp [w] at hvw
      rw [inner_smul_right] at hvw
      linarith only [hvw]
    refine ⟨r⁻¹ • v, ?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hvnorm]
      exact inv_mul_cancel₀ hr.ne'
    · simp [inner_smul_left, hvd]
    · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      dsimp [v]
      abel
  · rintro ⟨q, hqn, hqd, hD⟩
    have hv : v = r • q := by
      dsimp [v]
      rw [hD]
      abel
    have hvn : ‖v‖ = r := by
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hqn, mul_one]
    have hvw : inner ℝ v w = 0 := by
      dsimp [w]
      rw [hv]
      simp [inner_smul_left, inner_smul_right, hqd]
    have haa := norm_add_sq_real v w
    have hbb := norm_sub_sq_real v w
    rw [hvn, hvw, hw] at haa hbb
    have hna : ‖v + w‖ = 1 := by nlinarith only [haa, hrsq, norm_nonneg (v + w)]
    have hnb : ‖v - w‖ = 1 := by nlinarith only [hbb, hrsq, norm_nonneg (v - w)]
    constructor
    · rw [dist_eq_norm, hDp, hna]
    · rw [dist_eq_norm, hDp', hnb]
