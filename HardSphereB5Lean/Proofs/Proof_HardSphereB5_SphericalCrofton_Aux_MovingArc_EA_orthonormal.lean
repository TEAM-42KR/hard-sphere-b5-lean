import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc

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

theorem proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal (D : Pt) (hoff : offAxis D) : Orthonormal ℝ (EA D) := by
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
