import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_orthogonal_phase_inverse
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_arg_inverse (D p p' : Pt) (h0 : 0 < dist p p') (hz : dist p p' < 2)
    (hA : dist D p = 1) (hB : dist D p' = 1)
    (hf : centerFrame0 (p'-p) ≠ 0) :
    midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) •
      (Real.cos (Complex.arg (centerPhase D p p')) • centerFrame0 (p'-p) +
        Real.sin (Complex.arg (centerPhase D p p')) • centerFrame1 (p'-p)) = D := by
  let d := p'-p
  let m := midpoint ℝ p p'
  let R := Real.sqrt (1-dist p p'^2/4)
  have hd : d ≠ 0 := by
    intro h
    have h' : p'=p := sub_eq_zero.mp h
    rw [h', dist_self] at h0
    linarith
  obtain ⟨q, hqn, hqd, hD⟩ :=
    (HardSphereB5.SphericalCrofton.Aux.Coarea.center_circle_iff p p' D hz).mp ⟨hA,hB⟩
  have hr : 0 ≤ R := Real.sqrt_nonneg _
  have hw : D-m = R • q := by change D-m = R • q; rw [hD]; abel
  have hwn : ‖D-m‖ = R := by rw [hw, norm_smul, hqn, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
  have hqd' : inner ℝ d q = 0 := by
    simpa only [real_inner_comm] using hqd
  have horth : inner ℝ (unitDir d) (D-m) = 0 := by
    rw [hw, unitDir, real_inner_smul_left, real_inner_smul_right, hqd']
    ring
  have hframe : Orthonormal ℝ ![centerFrame0 d, centerFrame1 d, unitDir d] :=
    HardSphereB5.SphericalCrofton.Aux.Coarea.center_frame_orthonormal d hd hf
  have h := HardSphereB5.SphericalCrofton.Aux.Coarea.orthogonal_phase_inverse
    ![centerFrame0 d, centerFrame1 d, unitDir d] hframe (D-m) horth
  change ‖D-m‖ • (Real.cos (Complex.arg (phase (inner ℝ (centerFrame0 d) (D-m))
    (inner ℝ (centerFrame1 d) (D-m)))) • centerFrame0 d +
    Real.sin (Complex.arg (phase (inner ℝ (centerFrame0 d) (D-m))
    (inner ℝ (centerFrame1 d) (D-m)))) • centerFrame1 d) = D-m at h
  rw [hwn] at h
  change m + R • (Real.cos (Complex.arg (phase (inner ℝ (centerFrame0 d) (D-m))
      (inner ℝ (centerFrame1 d) (D-m)))) • centerFrame0 d +
    Real.sin (Complex.arg (phase (inner ℝ (centerFrame0 d) (D-m))
      (inner ℝ (centerFrame1 d) (D-m)))) • centerFrame1 d) = D
  rw [h]
  abel
