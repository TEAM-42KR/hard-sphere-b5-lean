import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff
set_option autoImplicit false

open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_center_geometry (y : Chart5)
    (hz0 : 0 < dist (targetEndpointA y) (targetEndpointB y))
    (hz2 : dist (targetEndpointA y) (targetEndpointB y) < 2)
    (hf : centerFrame0 (targetEndpointB y-targetEndpointA y) ≠ 0)
    (hψ : y 4 ∈ Set.Ioo (-Real.pi) Real.pi) :
    dist (targetCenter y) (targetEndpointA y) = 1 ∧
    dist (targetCenter y) (targetEndpointB y) = 1 ∧
    Complex.arg (centerPhase (targetCenter y) (targetEndpointA y) (targetEndpointB y)) = y 4 ∧
    centerPhase (targetCenter y) (targetEndpointA y) (targetEndpointB y) ∈ Complex.slitPlane := by
  let p := targetEndpointA y
  let p' := targetEndpointB y
  let d := p'-p
  let r := Real.sqrt (1-dist p p'^2/4)
  let F0 := centerFrame0 d
  let F1 := centerFrame1 d
  let q := Real.cos (y 4) • F0 + Real.sin (y 4) • F1
  have hd : d ≠ 0 := sub_ne_zero.mpr (dist_pos.mp hz0).symm
  have hb := center_frame_orthonormal d hd hf
  have hi := orthonormal_iff_ite.mp hb
  have h00 : inner ℝ F0 F0 = 1 := by simpa [F0] using hi 0 0
  have h11 : inner ℝ F1 F1 = 1 := by simpa [F1] using hi 1 1
  have h01 : inner ℝ F0 F1 = 0 := by simpa [F0,F1] using hi 0 1
  have h10 : inner ℝ F1 F0 = 0 := by simpa [F0,F1] using hi 1 0
  have h0n : inner ℝ F0 (unitDir d) = 0 := by simpa [F0] using hi 0 2
  have h1n : inner ℝ F1 (unitDir d) = 0 := by simpa [F1] using hi 1 2
  have hq2 : ‖q‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [q, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, h00,h11,h01,h10, mul_one,mul_zero,zero_mul,
      add_zero,zero_add]
    nlinarith [Real.sin_sq_add_cos_sq (y 4)]
  have hqn : ‖q‖ = 1 := by nlinarith [norm_nonneg q]
  have hqd : inner ℝ q d = 0 := by
    have hdn : d = ‖d‖ • unitDir d := by
      simp [unitDir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd)]
    rw [hdn, real_inner_smul_right]
    simp [q, inner_add_left, real_inner_smul_left, h0n,h1n]
  have hD : targetCenter y = midpoint ℝ p p' + r • q := rfl
  have hdist := (center_circle_iff p p' (targetCenter y) hz2).2 ⟨q,hqn,hqd,hD⟩
  have hr : 0 < r := by
    apply Real.sqrt_pos.mpr
    have hnon : 0 ≤ dist p p' := dist_nonneg
    nlinarith [hz2]
  have hp : centerPhase (targetCenter y) p p' =
      (r : ℂ) * ((Real.cos (y 4) : ℂ) + (Real.sin (y 4) : ℂ) * Complex.I) := by
    have hdiff : targetCenter y - midpoint ℝ p p' = r • q := by rw [hD]; abel
    change phase (inner ℝ F0 (targetCenter y - midpoint ℝ p p'))
      (inner ℝ F1 (targetCenter y - midpoint ℝ p p')) = _
    rw [hdiff]
    have hx : inner ℝ F0 (r • q) = r * Real.cos (y 4) := by
      simp only [real_inner_smul_right,q,inner_add_right,h00,h01,
        mul_one,mul_zero,add_zero]
    have hy : inner ℝ F1 (r • q) = r * Real.sin (y 4) := by
      simp only [real_inner_smul_right,q,inner_add_right,h10,h11,
        mul_one,mul_zero,zero_add]
    rw [hx,hy]
    apply Complex.ext <;>
      simp only [phase,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
  have harg : Complex.arg (centerPhase (targetCenter y) p p') = y 4 := by
    rw [hp]
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I hr ⟨hψ.1,hψ.2.le⟩
  refine ⟨hdist.1,hdist.2,harg,Complex.mem_slitPlane_iff_arg.mpr ⟨?_,?_⟩⟩
  · rw [harg]
    exact ne_of_lt hψ.2
  · intro hz
    have hre : r * Real.cos (y 4) = 0 := by
      have hh := congrArg Complex.re hz
      rw [hp] at hh
      simpa only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        Complex.zero_re,Complex.zero_im,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero] using hh
    have him : r * Real.sin (y 4) = 0 := by
      have hh := congrArg Complex.im hz
      rw [hp] at hh
      simpa only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        Complex.zero_re,Complex.zero_im,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero] using hh
    have hc := (mul_eq_zero.mp hre).resolve_left (ne_of_gt hr)
    have hs := (mul_eq_zero.mp him).resolve_left (ne_of_gt hr)
    have hh := Real.sin_sq_add_cos_sq (y 4)
    rw [hc,hs] at hh
    norm_num at hh
