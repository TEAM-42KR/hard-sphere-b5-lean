import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal (d : Pt) (hd : d ≠ 0) (hr : centerFrame0 d ≠ 0) :
    Orthonormal ℝ ![centerFrame0 d, centerFrame1 d, unitDir d] := by
  let r : Pt := e - (inner ℝ (unitDir d) e) • unitDir d
  have hn : ‖unitDir d‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg d),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd)]
  have hraw : r ≠ 0 := by
    intro hz
    apply hr
    change unitDir r = 0
    simp [unitDir, hz]
  have hf : ‖centerFrame0 d‖ = 1 := by
    change ‖unitDir r‖ = 1
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg r),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hraw)]
  have hnr : inner ℝ (unitDir d) r = 0 := by
    dsimp only [r]
    simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring
  have hnf : inner ℝ (unitDir d) (centerFrame0 d) = 0 := by
    change inner ℝ (unitDir d) ((‖r‖)⁻¹ • r) = 0
    rw [real_inner_smul_right, hnr, mul_zero]
  have hc : ‖centerFrame1 d‖ ^ 2 = 1 := by
    rw [centerFrame1, SphereGeom.Aux.Santalo.cross_norm_sq, hn, hf, hnf]
    norm_num
  have hf1 : inner ℝ (centerFrame0 d) (centerFrame1 d) = 0 := by
    simp [centerFrame1, SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
    ring
  have hn1 : inner ℝ (unitDir d) (centerFrame1 d) = 0 := by
    simp [centerFrame1, SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
    ring
  have hfn : inner ℝ (centerFrame0 d) (unitDir d) = 0 := by
    rw [real_inner_comm, hnf]
  have h1f : inner ℝ (centerFrame1 d) (centerFrame0 d) = 0 := by
    rw [real_inner_comm, hf1]
  have h1n : inner ℝ (centerFrame1 d) (unitDir d) = 0 := by
    rw [real_inner_comm, hn1]
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [real_inner_self_eq_norm_sq, hf, hc, hn, hnf, hf1, hn1, hfn, h1f, h1n]
