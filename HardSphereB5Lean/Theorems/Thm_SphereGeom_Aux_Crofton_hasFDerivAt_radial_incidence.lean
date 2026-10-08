import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_hasFDerivAt_radial_incidence
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.hasFDerivAt_radial_incidence :
    ∀ (a b : ℝ → E3) (ap bp : E3) (x : E3)
    (ha : HasDerivAt a ap (x 0)) (hb : HasDerivAt b bp (x 0)), HasFDerivAt (fun y : E3 => y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0)))
      ((PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 2).smulRight
        (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) +
        (x 2) • (((-Real.sin (x 1)) •
          (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 1)).smulRight (a (x 0)) +
          (Real.cos (x 1)) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ap).comp
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 0)) +
          ((Real.cos (x 1)) •
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 1)).smulRight (b (x 0)) +
          (Real.sin (x 1)) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) bp).comp
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 0)))) x :=
  @proof_SphereGeom_Aux_Crofton_hasFDerivAt_radial_incidence
