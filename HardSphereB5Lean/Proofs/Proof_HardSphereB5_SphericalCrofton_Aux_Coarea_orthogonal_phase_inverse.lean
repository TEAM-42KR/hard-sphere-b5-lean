import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_orthogonal_phase_inverse (f : Fin 3 → Pt) (hf : Orthonormal ℝ f) (w : Pt)
    (hw : inner ℝ (f 2) w = 0) :
    ‖w‖ • (Real.cos (Complex.arg (phase (inner ℝ (f 0) w) (inner ℝ (f 1) w))) • f 0 +
      Real.sin (Complex.arg (phase (inner ℝ (f 0) w) (inner ℝ (f 1) w))) • f 1) = w := by
  let b : OrthonormalBasis (Fin 3) ℝ Pt :=
    OrthonormalBasis.mk hf
      (hf.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [HardSphereB5.Lean.Pt])).ge
  have hb (i : Fin 3) : b i = f i := by simp [b]
  have hsum : inner ℝ (f 0) w • f 0 + inner ℝ (f 1) w • f 1 = w := by
    have h := b.sum_repr' w
    simpa [Fin.sum_univ_succ, hb, hw] using h
  let z : ℂ := phase (inner ℝ (f 0) w) (inner ℝ (f 1) w)
  have hnorm : ‖z‖ = ‖w‖ := by
    have h := b.sum_sq_norm_inner_right w
    simp [Fin.sum_univ_succ, hb, hw, Real.norm_eq_abs, sq_abs] at h
    have hz : ‖z‖ ^ 2 = inner ℝ (f 0) w ^ 2 + inner ℝ (f 1) w ^ 2 := by
      change ‖(⟨inner ℝ (f 0) w, inner ℝ (f 1) w⟩ : ℂ)‖ ^ 2 = _
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]
    nlinarith [norm_nonneg z, norm_nonneg w]
  by_cases hw0 : w = 0
  · simp [hw0]
  · have hz0 : z ≠ 0 := by
      intro h
      have h' : ‖w‖ = 0 := by rw [← hnorm, h, norm_zero]
      exact hw0 (norm_eq_zero.mp h')
    change ‖w‖ • (Real.cos z.arg • f 0 + Real.sin z.arg • f 1) = w
    rw [Complex.cos_arg hz0, Complex.sin_arg, hnorm, smul_add, smul_smul, smul_smul]
    have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    have hmul (a : ℝ) : ‖w‖ * (a / ‖w‖) = a := by field_simp
    change (‖w‖ * ((inner ℝ (f 0) w) / ‖w‖)) • f 0 +
      (‖w‖ * ((inner ℝ (f 1) w) / ‖w‖)) • f 1 = w
    rw [hmul, hmul]
    exact hsum
