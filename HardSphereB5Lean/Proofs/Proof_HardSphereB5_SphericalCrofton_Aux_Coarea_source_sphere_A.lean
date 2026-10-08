import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
set_option maxHeartbeats 700000

private theorem cross_inner_first (a b : Pt) : inner ℝ a (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_A (D : Pt) (hoff : offAxis D) (hr : ‖D‖ < 2) (θ : ℝ) :
    ‖u D θ‖ = 1 ∧ ‖D+u D θ‖ = 1 := by
  have hD : D ≠ 0 := by intro h; exact hoff 0 (by simpa using h)
  have hn : ‖nAv D‖ = 1 := by
    simp [nAv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg D),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hD)]
  have ho : inner ℝ (nAv D) (rawA D) = 0 := by
    simp only [rawA, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have hon : inner ℝ (nAv D) (EA D 0) = 0 := by
    change inner ℝ (nAv D) (unitDir (rawA D)) = 0
    simp [unitDir, real_inner_smul_right, ho]
  have hot : inner ℝ (nAv D) (EA D 1) = 0 := by
    exact cross_inner_first _ _
  have hDform : D = (-‖D‖) • nAv D := by
    simp [nAv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD)]
  have hd0 : inner ℝ D (EA D 0) = 0 := by nth_rw 1 [hDform]; rw [real_inner_smul_left, hon]; ring
  have hd1 : inner ℝ D (EA D 1) = 0 := by nth_rw 1 [hDform]; rw [real_inner_smul_left, hot]; ring
  let q : Pt := Real.cos θ • EA D 0 + Real.sin θ • EA D 1
  have he := HardSphereB5.SphericalCrofton.Aux.MovingArc.EA_orthonormal D hoff
  have hi := orthonormal_iff_ite.mp he
  have hnorm (i : Fin 2) : ‖EA D i‖ = 1 := he.norm_eq_one i
  have hz01 : inner ℝ (EA D 0) (EA D 1) = 0 := by simpa using hi 0 1
  have hq : ‖q‖^2 = 1 := by
    have h := norm_add_sq_real (Real.cos θ • EA D 0) (Real.sin θ • EA D 1)
    rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hz01,
      hnorm 0, hnorm 1] at h
    simp only [mul_one, mul_zero, zero_mul, add_zero, Real.norm_eq_abs, sq_abs] at h
    change ‖q‖^2 = _ at h
    rw [h]
    exact Real.cos_sq_add_sin_sq θ
  have hdq : inner ℝ D q = 0 := by simp [q, inner_add_right, real_inner_smul_right, hd0,hd1]
  have hrad : 0 ≤ 1-‖D‖^2/4 := by nlinarith [norm_nonneg D]
  have hr2 : rA D ^ 2 = 1-‖D‖^2/4 := Real.sq_sqrt hrad
  have hu : u D θ = (-1/2 : ℝ) • D + rA D • q := rfl
  have hp : D+u D θ = (1/2 : ℝ) • D + rA D • q := by rw [hu]; module
  have hunit (s : ℝ) (hs : s^2 = 1/4) : ‖s • D + rA D • q‖ = 1 := by
    have h := norm_add_sq_real (s • D) (rA D • q)
    rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hdq] at h
    simp only [mul_zero, zero_mul, add_zero, mul_pow, Real.norm_eq_abs, sq_abs,
      hs, hq, hr2, mul_one] at h
    nlinarith [norm_nonneg (s • D + rA D • q)]
  constructor
  · rw [hu]; exact hunit (-1/2) (by norm_num)
  · rw [hp]; exact hunit (1/2) (by norm_num)
