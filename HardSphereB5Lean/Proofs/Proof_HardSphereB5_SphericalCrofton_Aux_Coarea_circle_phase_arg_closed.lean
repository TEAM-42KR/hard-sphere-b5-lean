import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section

set_option maxHeartbeats 700000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_circle_phase_arg_closed
    (f : Fin 2 → Pt) (hf : Orthonormal ℝ f) (c : Pt) (r θ : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi)
    (hslit : phase (inner ℝ (f 0) (circlePt c (f 0) (f 1) r θ - c))
      (inner ℝ (f 1) (circlePt c (f 0) (f 1) r θ - c)) ∈ Complex.slitPlane) :
    Complex.arg (phase (inner ℝ (f 0) (circlePt c (f 0) (f 1) r θ - c))
      (inner ℝ (f 1) (circlePt c (f 0) (f 1) r θ - c))) = θ := by
  have hi := orthonormal_iff_ite.mp hf
  have hn (i : Fin 2) : ‖f i‖ = 1 := hf.norm_eq_one i
  have hp : phase (inner ℝ (f 0) (circlePt c (f 0) (f 1) r θ-c))
      (inner ℝ (f 1) (circlePt c (f 0) (f 1) r θ-c)) =
      (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp [phase, circlePt, inner_add_right, real_inner_smul_right, hi, hn, mul_add,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hneg : θ ≠ -Real.pi := by
    intro heq
    apply Complex.slitPlane_arg_ne_pi hslit
    rw [hp, heq]
    simp only [Real.cos_neg, Real.cos_pi, Real.sin_neg, Real.sin_pi,
      neg_zero, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero,
      zero_mul, add_zero, mul_neg, mul_one]
    simpa only [Complex.ofReal_neg] using
      Complex.arg_ofReal_of_neg (by linarith : -r < 0)
  rw [hp]
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I hr ⟨lt_of_le_of_ne hθ.1 hneg.symm, hθ.2⟩
