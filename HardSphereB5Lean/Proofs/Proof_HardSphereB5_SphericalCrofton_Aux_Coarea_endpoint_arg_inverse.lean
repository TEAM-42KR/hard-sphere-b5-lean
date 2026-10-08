import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false

open HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_arg_inverse (p : Pt) (hp : ‖p‖ = 1) (h0 : |p 0| < 1) :
    (Real.sqrt (1 - (p 0)^2) * Real.cos (Complex.arg ((p 1 : ℂ) + Complex.I * (p 2 : ℂ)))) • e1 +
    (Real.sqrt (1 - (p 0)^2) * Real.sin (Complex.arg ((p 1 : ℂ) + Complex.I * (p 2 : ℂ)))) • e2 +
    (p 0) • e = p := by
  let z : ℂ := (p 1 : ℂ) + Complex.I * (p 2 : ℂ)
  have hsum : (p 0)^2 + ((p 1)^2 + (p 2)^2) = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq p
    rw [hp] at h
    simpa [Fin.sum_univ_succ] using h.symm
  have hpos : 0 < 1 - (p 0)^2 := by
    have h := mul_self_lt_mul_self (abs_nonneg (p 0)) h0
    nlinarith [sq_abs (p 0)]
  have hznorm : ‖z‖ = Real.sqrt (1 - (p 0)^2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp [z]
    nlinarith [hsum]
  have hz : z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hznorm]
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  have hc : Real.sqrt (1 - (p 0)^2) * Real.cos z.arg = p 1 := by
    rw [Complex.cos_arg hz, ← hznorm, show z.re = p 1 by simp [z]]
    field_simp [norm_ne_zero_iff.mpr hz]
  have hs : Real.sqrt (1 - (p 0)^2) * Real.sin z.arg = p 2 := by
    rw [Complex.sin_arg, ← hznorm, show z.im = p 2 by simp [z]]
    field_simp [norm_ne_zero_iff.mpr hz]
  change (Real.sqrt (1 - (p 0)^2) * Real.cos z.arg) • e1 +
    (Real.sqrt (1 - (p 0)^2) * Real.sin z.arg) • e2 + (p 0) • e = p
  rw [hc, hs]
  ext i
  fin_cases i <;> simp [e, e1, e2]
