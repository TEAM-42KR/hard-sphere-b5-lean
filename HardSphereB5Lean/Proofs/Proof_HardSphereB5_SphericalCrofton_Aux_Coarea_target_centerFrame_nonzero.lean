import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section
set_option maxHeartbeats 900000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_centerFrame_nonzero
    (y : Chart5) (h0 : |y 0| < 1) (h2 : |y 2| < 1)
    (h1 : y 1 ∈ Set.Ioo (-Real.pi) Real.pi) (h3 : y 3 ∈ Set.Ioo (-Real.pi) Real.pi)
    (h13 : y 1 ≠ y 3) : centerFrame0 (targetEndpointB y-targetEndpointA y) ≠ 0 := by
  let p := targetEndpointA y
  let q := targetEndpointB y
  let d := q-p
  have hr (h : ℝ) (hh : |h| < 1) : 0 < Real.sqrt (1-h^2) := by
    apply Real.sqrt_pos.mpr
    have hs := mul_self_lt_mul_self (abs_nonneg h) hh
    nlinarith [sq_abs h]
  have hphase (r θ : ℝ) : phase (r*Real.cos θ) (r*Real.sin θ) =
      (r : ℂ) * ((Real.cos θ : ℂ)+(Real.sin θ : ℂ)*Complex.I) := by
    apply Complex.ext <;>
      simp only [phase,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
  have hargA : azimuth p = y 1 := by
    have hp : phase (p 1) (p 2) = phase (Real.sqrt (1-(y 0)^2)*Real.cos (y 1))
      (Real.sqrt (1-(y 0)^2)*Real.sin (y 1)) := by
      simp [p,targetEndpointA,endpointCylinder,e,e1,e2]
    unfold azimuth
    rw [hp,hphase]
    simpa only [← Complex.ofReal_cos,← Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I (hr _ h0) ⟨h1.1,h1.2.le⟩
  have hargB : azimuth q = y 3 := by
    have hq : phase (q 1) (q 2) = phase (Real.sqrt (1-(y 2)^2)*Real.cos (y 3))
      (Real.sqrt (1-(y 2)^2)*Real.sin (y 3)) := by
      simp [q,targetEndpointB,endpointCylinder,e,e1,e2]
    unfold azimuth
    rw [hq,hphase]
    simpa only [← Complex.ofReal_cos,← Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I (hr _ h2) ⟨h3.1,h3.2.le⟩
  intro hf
  have hraw : e-(inner ℝ (unitDir d) e) • unitDir d = 0 := by
    change unitDir (e-(inner ℝ (unitDir d) e) • unitDir d) = 0 at hf
    simpa only [unitDir,smul_eq_zero,inv_eq_zero,norm_eq_zero,or_self] using hf
  have heq := sub_eq_zero.mp hraw
  have hs : inner ℝ (unitDir d) e ≠ 0 := by
    intro hs
    rw [hs,zero_smul] at heq
    have h := congrArg norm heq
    norm_num [e] at h
  have hd : d ≠ 0 := by
    intro hd
    simp [hd,unitDir] at heq
    have h := congrArg norm heq
    norm_num [e] at h
  have hpar : d = (‖d‖*(inner ℝ (unitDir d) e)⁻¹) • e := by
    calc
      d = ‖d‖ • unitDir d := by
        simp [unitDir,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd)]
      _ = (‖d‖*(inner ℝ (unitDir d) e)⁻¹) •
          ((inner ℝ (unitDir d) e) • unitDir d) := by
        rw [smul_smul,mul_assoc,inv_mul_cancel₀ hs,mul_one]
      _ = (‖d‖*(inner ℝ (unitDir d) e)⁻¹) • e := by rw [← heq]
  have hc1 : q 1 = p 1 := by
    have h := congrArg (fun x : Pt => x (1 : Fin 3)) hpar
    simpa [d,e,sub_eq_zero] using h
  have hc2 : q 2 = p 2 := by
    have h := congrArg (fun x : Pt => x (2 : Fin 3)) hpar
    simpa [d,e,sub_eq_zero] using h
  apply h13
  rw [← hargA,← hargB]
  unfold azimuth
  rw [hc1,hc2]
