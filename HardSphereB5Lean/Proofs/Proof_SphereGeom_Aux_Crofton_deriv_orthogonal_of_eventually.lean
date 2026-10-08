import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_deriv_orthogonal_of_eventually (u γ : ℝ → E3) (s : ℝ)
    (hu : DifferentiableAt ℝ u s) (hγ : DifferentiableAt ℝ γ s)
    (he : (fun t => inner ℝ (u t) (γ t)) =ᶠ[nhds s] (fun _ => 0)) :
    inner ℝ (deriv u s) (γ s) = -inner ℝ (u s) (deriv γ s) := by
  have hprod := hu.hasDerivAt.inner ℝ hγ.hasDerivAt
  have hzero : HasDerivAt (fun t => inner ℝ (u t) (γ t)) 0 s :=
    (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq he
  have hd := hprod.unique hzero
  linarith
