import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_deriv_tangent_sphere_Ioo (γ : ℝ → E3) (a b s : ℝ)
    (hs : ∀ t ∈ Set.Icc a b, ‖γ t‖ = 1)
    (hγ : DifferentiableAt ℝ γ s) (hst : s ∈ Set.Ioo a b) :
    inner ℝ (deriv γ s) (γ s) = 0 := by
  have he : (fun t => inner ℝ (γ t) (γ t)) =ᶠ[nhds s] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hst] with t ht
    rw [real_inner_self_eq_norm_sq, hs t (Set.Ioo_subset_Icc_self ht)]
    norm_num
  have hd := (hγ.hasDerivAt.inner ℝ hγ.hasDerivAt).unique
    ((hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq he)
  rw [real_inner_comm (deriv γ s) (γ s)] at hd
  linarith
