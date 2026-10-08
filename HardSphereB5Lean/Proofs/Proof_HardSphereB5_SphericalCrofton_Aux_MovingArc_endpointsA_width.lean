import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem cross_norm_sq_native (a b : Pt) :
    ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - inner ℝ a b ^ 2 := by
  simp [SphereGeom.cross, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    cross_apply, Fin.sum_univ_succ]
  ring

private theorem cross_inner_first (a b : Pt) : inner ℝ a (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem cross_inner_second (a b : Pt) : inner ℝ b (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem axisA_facts (D : Pt) (hoff : offAxis D) :
    D ≠ 0 ∧ ‖nAv D‖ = 1 ∧ rawA D ≠ 0 ∧
      inner ℝ (nAv D) (rawA D) = 0 := by
  have hD : D ≠ 0 := by
    intro hd
    exact hoff 0 (by simpa using hd)
  have hn : ‖nAv D‖ = 1 := by
    simp [nAv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg D),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hD)]
  have horth : inner ℝ (nAv D) (rawA D) = 0 := by
    simp only [rawA, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have he : ‖(e : Pt)‖ = 1 := by simp [e]
  have hraw : rawA D ≠ 0 := by
    intro hr
    have heq : e = (inner ℝ (nAv D) e) • nAv D := sub_eq_zero.mp hr
    have hcoeff : inner ℝ (nAv D) e ≠ 0 := by
      intro hc
      rw [hc, zero_smul] at heq
      have hbad := congrArg norm heq
      rw [he, norm_zero] at hbad
      norm_num at hbad
    have hDaxis : D = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by
      calc
        D = (-‖D‖) • nAv D := by
          simp [nAv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD)]
        _ = ((-‖D‖ * (inner ℝ (nAv D) e)⁻¹) * inner ℝ (nAv D) e) • nAv D := by
          rw [mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) •
            ((inner ℝ (nAv D) e) • nAv D) := by rw [smul_smul]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by rw [← heq]
    exact hoff _ hDaxis
  exact ⟨hD, hn, hraw, horth⟩

private theorem frameProof (D : Pt) (hoff : offAxis D) : Orthonormal ℝ (EA D) := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf : ‖unitDir (rawA D)‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (rawA D)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  have hnf : inner ℝ (nAv D) (unitDir (rawA D)) = 0 := by
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hc : ‖cross (nAv D) (unitDir (rawA D))‖ ^ 2 = 1 := by
    rw [cross_norm_sq_native, hn, hf, hnf]
    norm_num
  have hf0 : inner ℝ (unitDir (rawA D)) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    cross_inner_second _ _
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [EA, real_inner_self_eq_norm_sq, hf, hc, hf0, real_inner_comm]

private theorem movingA_radius (D : Pt) (hL : D ∈ LamC) :
    0 < rA D ∧ (rA D)^2 = 1-‖D‖^2/4 := by
  have hnorm : ‖D‖ ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall] using hL.1
  have hn0 := norm_nonneg D
  have hp : 0 < 1-‖D‖^2/4 := by nlinarith
  exact ⟨by simpa [rA] using Real.sqrt_pos.2 hp,
    by simpa [rA] using Real.sq_sqrt hp.le⟩

theorem proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_endpointsA_width (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (hRc : Rc ‖D‖ ‖D - e‖ < 1) :
    dist (u D (-(halfA D))) (u D (halfA D)) =
      2 * rA D * Real.sin (halfA D) := by
  have hf := frameProof D hoff
  have hr := (movingA_radius D hL).1
  have hh0 : 0 ≤ halfA D := Real.arccos_nonneg _
  have hhpi : halfA D ≤ Real.pi := Real.arccos_le_pi _
  have hs : 0 ≤ Real.sin (halfA D) := Real.sin_nonneg_of_nonneg_of_le_pi hh0 hhpi
  have hdiff : u D (-(halfA D)) - u D (halfA D) =
      (-(2 * rA D * Real.sin (halfA D))) • EA D 1 := by
    simp only [u, circlePt, Real.cos_neg, Real.sin_neg]
    module
  rw [dist_eq_norm, hdiff, norm_smul, hf.norm_eq_one 1,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), mul_one]
