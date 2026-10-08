import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option backward.isDefEq.respectTransparency false in
theorem proof_SphereGeom_Aux_Crofton_hasFDerivAt_radial_incidence (a b : ℝ → E3) (ap bp : E3) (x : E3)
    (ha : HasDerivAt a ap (x 0)) (hb : HasDerivAt b bp (x 0)) :
    HasFDerivAt (fun y : E3 => y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0)))
      ((PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 2).smulRight
        (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) +
        (x 2) • (((-Real.sin (x 1)) •
          (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 1)).smulRight (a (x 0)) +
          (Real.cos (x 1)) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ap).comp
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 0)) +
          ((Real.cos (x 1)) •
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 1)).smulRight (b (x 0)) +
          (Real.sin (x 1)) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) bp).comp
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 0)))) x := by
  let P (i : Fin 3) : E3 →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) i
  have h0 : HasFDerivAt (fun y : E3 => y 0) (P 0) x := (P 0).hasFDerivAt
  have h1 : HasFDerivAt (fun y : E3 => y 1) (P 1) x := (P 1).hasFDerivAt
  have h2 : HasFDerivAt (fun y : E3 => y 2) (P 2) x := (P 2).hasFDerivAt
  have ha' := ha.hasFDerivAt.comp x h0
  have hb' := hb.hasFDerivAt.comp x h0
  have hc := (Real.hasDerivAt_cos (x 1)).comp_hasFDerivAt x h1
  have hs := (Real.hasDerivAt_sin (x 1)).comp_hasFDerivAt x h1
  apply (h2.smul ((hc.smul ha').add (hs.smul hb'))).congr_fderiv
  ext y i
  simp only [P, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.one_apply,
    PiLp.proj_apply, smul_add, add_smul, smul_smul, add_assoc,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Function.comp_apply,
    Pi.add_apply, Pi.smul_apply, Pi.smul_apply']
  try dsimp only [Function.comp_def]
  try simp only [PiLp.add_apply, PiLp.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', smul_eq_mul]
  ring
