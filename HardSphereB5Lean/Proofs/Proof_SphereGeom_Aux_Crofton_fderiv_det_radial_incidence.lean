import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_hasFDerivAt_radial_incidence
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_radial_frame_det
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option backward.isDefEq.respectTransparency false in
theorem proof_SphereGeom_Aux_Crofton_fderiv_det_radial_incidence (a b : ℝ → E3) (ap bp g gp : E3) (x : E3)
    (ha : HasDerivAt a ap (x 0)) (hb : HasDerivAt b bp (x 0))
    (hab : cross (a (x 0)) (b (x 0)) = g)
    (hga : inner ℝ ap g = -inner ℝ (a (x 0)) gp)
    (hgb : inner ℝ bp g = -inner ℝ (b (x 0)) gp) :
    (fderiv ℝ (fun y : E3 => y 2 •
      (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))) x).det =
      (x 2) ^ 2 * inner ℝ (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) gp := by
  rw [(SphereGeom.Aux.Crofton.hasFDerivAt_radial_incidence a b ap bp x ha hb).fderiv]
  let e := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  unfold ContinuousLinearMap.det
  rw [← LinearMap.det_toMatrix e]
  have hmat : LinearMap.toMatrix e e
      (((PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 2).smulRight
        (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) +
        (x 2) • (((-Real.sin (x 1)) •
          (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 1)).smulRight (a (x 0)) +
          (Real.cos (x 1)) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ap).comp
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 0)) +
          ((Real.cos (x 1)) •
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 1)).smulRight (b (x 0)) +
          (Real.sin (x 1)) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) bp).comp
            (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) 0)))) : E3 →ₗ[ℝ] E3) =
        (fun i j : Fin 3 => (![x 2 • (Real.cos (x 1) • ap + Real.sin (x 1) • bp),
          x 2 • (-Real.sin (x 1) • a (x 0) + Real.cos (x 1) • b (x 0)),
          Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)] : Fin 3 → E3) j i) := by
    ext i j
    fin_cases j <;>
      simp [LinearMap.toMatrix_apply, e, EuclideanSpace.basisFun_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, sub_eq_add_neg]
    all_goals ring
  trans Matrix.det (fun i j : Fin 3 => (![x 2 • (Real.cos (x 1) • ap + Real.sin (x 1) • bp),
      x 2 • (-Real.sin (x 1) • a (x 0) + Real.cos (x 1) • b (x 0)),
      Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)] : Fin 3 → E3) j i)
  · exact congrArg Matrix.det hmat
  · exact SphereGeom.Aux.Crofton.radial_frame_det (a (x 0)) (b (x 0)) g ap bp gp (x 2) (x 1) hab hga hgb
