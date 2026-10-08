import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_phase_fderiv (a b : ℝ) (hz : phase a b ∈ Complex.slitPlane) :
    HasFDerivAt (fun p : ℝ × ℝ => Complex.arg (phase p.1 p.2))
      ((a / (a^2+b^2)) • (ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (b / (a^2+b^2)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) (a,b) := by
  let P : (ℝ × ℝ) →L[ℝ] ℂ := Complex.equivRealProdCLM.symm.toContinuousLinearMap
  have hP : HasFDerivAt (fun p : ℝ × ℝ => phase p.1 p.2) P (a,b) := by
    exact P.hasFDerivAt
  have hlog := (Complex.hasStrictFDerivAt_log_real hz).hasFDerivAt
  have h := Complex.imCLM.hasFDerivAt.comp (phase a b) hlog
  have hc := h.comp (a,b) hP
  have hL : (Complex.imCLM.comp ((phase a b)⁻¹ • (1 : ℂ →L[ℝ] ℂ))).comp P =
      (a / (a^2+b^2)) • (ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (b / (a^2+b^2)) • (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro p
    change (((phase a b)⁻¹) * (phase p.1 p.2)).im =
      (a / (a^2+b^2)) * p.2 - (b / (a^2+b^2)) * p.1
    rw [Complex.mul_im, Complex.inv_re, Complex.inv_im]
    change (a / (a*a+b*b)) * p.2 + (-b / (a*a+b*b)) * p.1 = _
    ring
  rw [hL] at hc
  simpa [Function.comp_def, Complex.imCLM, Complex.log_im] using hc
