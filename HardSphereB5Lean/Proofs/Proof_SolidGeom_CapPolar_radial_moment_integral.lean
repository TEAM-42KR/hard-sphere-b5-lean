import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
set_option maxHeartbeats 1000000
theorem proof_SolidGeom_CapPolar_radial_moment_integral (p a b : SphereGeom.E3) (ψ R : ℝ) :
    (∫ ρ in (0)..R, Real.sin ρ • SolidGeom.CapPolar.polarRay p a b ψ ρ)=
      ((R-Real.sin R*Real.cos R)/2) • SolidGeom.CapPolar.capDirection a b ψ+
      ((Real.sin R)^2/2) • p  := by
  let D := capDirection a b ψ
  let F : ℝ → E3 := fun x => ((x-Real.sin x*Real.cos x)/2) • D+(Real.sin x^2/2) • p
  have hd (x : ℝ) : HasDerivAt F (Real.sin x • polarRay p a b ψ x) x := by
    have hD := (((hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x))).div_const 2).smul_const D
    have hp := (((Real.hasDerivAt_sin x).pow 2).div_const 2).smul_const p
    have h := hD.add hp
    apply h.congr_deriv
    simp only [one_div,one_mul,mul_one,mul_neg,sub_neg_eq_add]
    ext k
    simp only [PiLp.add_apply,PiLp.smul_apply,polarRay,smul_eq_mul,D,capDirection]
    nlinarith [congrArg (fun z : ℝ => z*(Real.cos ψ*a k+Real.sin ψ*b k)) (Real.sin_sq_add_cos_sq x)]
  have hi : IntervalIntegrable (fun x => Real.sin x • polarRay p a b ψ x) volume 0 R := by
    apply Continuous.intervalIntegrable
    unfold polarRay
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  simpa only [F,Real.sin_zero,Real.cos_zero,mul_zero,zero_mul,sub_zero,zero_div,zero_pow (by decide : 2≠0),zero_smul,
    zero_add,D] using hFTC
#print axioms proof_SolidGeom_CapPolar_radial_moment_integral
