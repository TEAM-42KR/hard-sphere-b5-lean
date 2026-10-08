import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_parameter_volume_eq_prod
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_frame_radial_angle_prod_lintegral
set_option autoImplicit false

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_parameter_frame_weighted_lintegral (S : Set ℝ) (hS : MeasurableSet S)
    (f : ℝ → ENNReal) (hf : Measurable f)
    (a b g v : ℝ → E3) (ha : Measurable a) (hb : Measurable b)
    (hg : Measurable g) (hv : Measurable v)
    (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, g s])
    (hvg : ∀ s ∈ S, inner ℝ (v s) (g s) = 0) :
    (∫⁻ x : E3 in {x | x 0 ∈ S ∧ x 1 ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) ∧
        x 2 ∈ Set.Ioo (0 : ℝ) 1},
      f (x 0) * ENNReal.ofReal ((x 2) ^ 2 *
        |inner ℝ (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) (v (x 0))|)) =
      (4 / 3 : ENNReal) * ∫⁻ s in S, f s * ENNReal.ofReal ‖v s‖ := by
  let H (s : ℝ) (q : ℝ × ℝ) : ENNReal :=
    ENNReal.ofReal (q.1 ^ 2 *
      |inner ℝ (Real.cos q.2 • a s + Real.sin q.2 • b s) (v s)|)
  let F (p : ℝ × (ℝ × ℝ)) : ENNReal := f p.1 * H p.1 p.2.swap
  have hF : Measurable F := by dsimp [F, H]; fun_prop
  have hH (s : ℝ) : Measurable (H s) := by dsimp [H]; fun_prop
  have hfiber (s : ℝ) (hs : s ∈ S) :
      (∫⁻ q : ℝ × ℝ in Set.Ioc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Ioo (0 : ℝ) 1,
        H s q.swap ∂(volume.prod volume)) =
        (4 / 3 : ENNReal) * ENNReal.ofReal ‖v s‖ := by
    rw [← Measure.prod_restrict,
      ← (restrict_Ioo_eq_restrict_Ioc (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)),
      lintegral_prod_swap, Measure.prod_restrict]
    exact SphereGeom.Aux.Crofton.frame_radial_angle_prod_lintegral
      (a s) (b s) (g s) (v s) (hframe s hs) (hvg s hs)
  calc
    _ = ∫⁻ p : ℝ × (ℝ × ℝ) in S ×ˢ
          (Set.Ioc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Ioo (0 : ℝ) 1), F p
          ∂(volume.prod (volume.prod volume)) := by
      exact SphereGeom.Aux.Crofton.parameter_volume_eq_prod S _ _ hS
        measurableSet_Ioc measurableSet_Ioo F hF
    _ = ∫⁻ s in S, f s *
          (∫⁻ q : ℝ × ℝ in Set.Ioc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Ioo (0 : ℝ) 1,
            H s q.swap ∂(volume.prod volume)) := by
      rw [setLIntegral_prod F hF.aemeasurable]
      apply lintegral_congr
      intro s
      exact lintegral_const_mul (f s) ((hH s).comp measurable_swap)
    _ = ∫⁻ s in S, f s * ((4 / 3 : ENNReal) * ENNReal.ofReal ‖v s‖) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with s hs
      rw [hfiber s hs]
    _ = ∫⁻ s in S, (4 / 3 : ENNReal) * (f s * ENNReal.ofReal ‖v s‖) := by
      apply lintegral_congr
      intro s
      ring
    _ = (4 / 3 : ENNReal) * ∫⁻ s in S, f s * ENNReal.ofReal ‖v s‖ := by
      exact lintegral_const_mul (4 / 3 : ENNReal) (hf.mul hv.norm.ennreal_ofReal)
