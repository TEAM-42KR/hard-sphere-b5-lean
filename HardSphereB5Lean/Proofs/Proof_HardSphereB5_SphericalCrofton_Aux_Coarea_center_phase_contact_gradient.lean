import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_fderiv
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_orthogonal_phase_inverse
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_contact_gradient
    (D p p' : Pt) (hz0 : 0 < dist p p') (hz2 : dist p p' < 2)
    (hDp : dist D p = 1) (hDp' : dist D p' = 1)
    (hframe : centerFrame0 (p'-p) ≠ 0)
    (hphase : centerPhase D p p' ∈ Complex.slitPlane) :
    HasFDerivAt (fun W : Pt => Complex.arg (centerPhase W p p'))
      ((dist p p' * (1 - dist p p' ^ 2 / 4))⁻¹ •
        (innerSL ℝ (cross (p-D) (p'-D)))) D := by
  let d : Pt := p'-p
  let z : ℝ := dist p p'
  let R : ℝ := 1-z^2/4
  let n : Pt := unitDir d
  let f : Pt := centerFrame0 d
  let g : Pt := centerFrame1 d
  let X : Pt := D-midpoint ℝ p p'
  let A : ℝ := inner ℝ f X
  let B : ℝ := inner ℝ g X
  have hz : 0 < z := hz0
  have hR : 0 < R := by dsimp [R,z]; nlinarith
  have hd : d ≠ 0 := by
    intro he
    have hp := sub_eq_zero.mp he
    have heq : p = p' := hp.symm
    rw [heq, dist_self] at hz0
    exact (lt_irrefl 0) hz0
  have hdnorm : ‖d‖ = z := by
    dsimp [d,z]
    rw [dist_eq_norm, norm_sub_rev]
  have hbasis : Orthonormal ℝ ![f,g,n] :=
    HardSphereB5.SphericalCrofton.Aux.Coarea.center_frame_orthonormal d hd hframe
  have hff : inner ℝ f f = 1 := by
    simpa using (orthonormal_iff_ite.mp hbasis) (0 : Fin 3) (0 : Fin 3)
  have hgg : inner ℝ g g = 1 := by
    simpa using (orthonormal_iff_ite.mp hbasis) (1 : Fin 3) (1 : Fin 3)
  have hfg : inner ℝ f g = 0 := by
    simpa using (orthonormal_iff_ite.mp hbasis) (0 : Fin 3) (1 : Fin 3)
  have hgf : inner ℝ g f = 0 := by rw [real_inner_comm, hfg]
  have hnn : inner ℝ n n = 1 := by
    simpa using (orthonormal_iff_ite.mp hbasis) (2 : Fin 3) (2 : Fin 3)
  have hnf : inner ℝ n f = 0 := by
    simpa using (orthonormal_iff_ite.mp hbasis) (2 : Fin 3) (0 : Fin 3)
  obtain ⟨w,hw,hwperp,hDw⟩ :=
    (HardSphereB5.SphericalCrofton.Aux.Coarea.center_circle_iff p p' D hz2).mp ⟨hDp,hDp'⟩
  have hXw : X = Real.sqrt R • w := by
    dsimp only [X]
    rw [hDw, add_sub_cancel_left]
  have hnX : inner ℝ n X = 0 := by
    rw [hXw]
    have hwrev : inner ℝ d w = 0 := by simpa [d,real_inner_comm] using hwperp
    change inner ℝ (‖d‖⁻¹ • d) (Real.sqrt R • w) = 0
    simp [real_inner_smul_left, real_inner_smul_right, hwrev]
  have hXnorm : ‖X‖^2 = R := by
    rw [hXw, norm_smul, hw, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg R), Real.sq_sqrt (le_of_lt hR)]
  let θ : ℝ := Complex.arg (phase A B)
  have hrec : ‖X‖ • (Real.cos θ • f + Real.sin θ • g) = X := by
    simpa [θ,A,B] using
      HardSphereB5.SphericalCrofton.Aux.Coarea.orthogonal_phase_inverse ![f,g,n] hbasis X hnX
  have hA : ‖X‖ * Real.cos θ = A := by
    have h := congrArg (fun Y : Pt => inner ℝ f Y) hrec
    simpa only [inner_add_right, real_inner_smul_right, hff, hfg, mul_one,
      mul_zero, add_zero] using h
  have hB : ‖X‖ * Real.sin θ = B := by
    have h := congrArg (fun Y : Pt => inner ℝ g Y) hrec
    simpa only [inner_add_right, real_inner_smul_right, hgf, hgg, mul_one,
      mul_zero, zero_add] using h
  have hX : X = A • f + B • g := by
    rw [smul_add,smul_smul,smul_smul,hA,hB] at hrec
    exact hrec.symm
  have hden : A^2+B^2 = R := by
    rw [←hA,←hB]
    nlinarith [Real.cos_sq_add_sin_sq θ, hXnorm]
  have hnd : z • n = d := by
    dsimp only [n,unitDir]
    rw [hdnorm, smul_smul, mul_inv_cancel₀ (ne_of_gt hz), one_smul]
  have hnf_cross : cross n f = g := rfl
  have hng_cross : cross n g = -f := by
    have ht : cross n (cross n f) = (inner ℝ n f) • n - (inner ℝ n n) • f := by
      have hdotnf : dotProduct n.ofLp f.ofLp = inner ℝ n f := by
        change (∑ i : Fin 3, n i*f i) = ∑ i : Fin 3, f i*n i
        simp_rw [mul_comm]
      have hdotnn : dotProduct n.ofLp n.ofLp = inner ℝ n n := by rfl
      have h := cross_cross_eq_smul_sub_smul' (n.ofLp) (n.ofLp) (f.ofLp)
      rw [hdotnf,hdotnn] at h
      apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
      exact h
    rw [hnf,hnn,zero_smul,one_smul,zero_sub] at ht
    exact ht
  have hcross_linear (a b : ℝ) (v w : Pt) :
      cross n (a • v+b • w) = a • cross n v+b • cross n w := by
    ext i
    fin_cases i <;> simp [SphereGeom.cross,cross_apply] <;> ring
  have hcross_scale (a : ℝ) (v w : Pt) : cross (a • v) w = a • cross v w := by
    ext i
    fin_cases i <;> simp [SphereGeom.cross,cross_apply] <;> ring
  have hgeometry : cross (p-D) (p'-D) = cross d X := by
    ext i
    fin_cases i <;> simp [d,X,midpoint_eq_smul_add,SphereGeom.cross,cross_apply] <;> ring
  have hcross : cross (p-D) (p'-D) = z • (A • g-B • f) := by
    rw [hgeometry,←hnd,hcross_scale,hX,hcross_linear,hnf_cross,hng_cross]
    simp [sub_eq_add_neg]
  have hmap : (A/(A^2+B^2)) • (innerSL ℝ g) - (B/(A^2+B^2)) • (innerSL ℝ f) =
      (z*R)⁻¹ • (innerSL ℝ (cross (p-D) (p'-D))) := by
    ext w
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      innerSL_apply_apply,smul_eq_mul]
    rw [hden,hcross]
    simp only [real_inner_smul_left,inner_sub_left]
    field_simp [ne_of_gt hz,ne_of_gt hR] <;> ring
  have hder : HasFDerivAt (fun W : Pt => Complex.arg (centerPhase W p p'))
      ((A/(A^2+B^2)) • (innerSL ℝ g) - (B/(A^2+B^2)) • (innerSL ℝ f)) D :=
    HardSphereB5.SphericalCrofton.Aux.Coarea.center_phase_fderiv D p p' hphase
  rw [hmap] at hder
  exact hder

