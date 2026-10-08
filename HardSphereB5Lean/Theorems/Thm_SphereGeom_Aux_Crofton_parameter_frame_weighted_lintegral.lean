import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_parameter_frame_weighted_lintegral
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.parameter_frame_weighted_lintegral :
    ∀ (S : Set ℝ) (hS : MeasurableSet S) (f : ℝ → ENNReal) (hf : Measurable f) (a b g v : ℝ → E3) (ha : Measurable a) (hb : Measurable b) (hg : Measurable g) (hv : Measurable v) (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, g s]) (hvg : ∀ s ∈ S, inner ℝ (v s) (g s) = 0), (∫⁻ x : E3 in {x | x 0 ∈ S ∧ x 1 ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) ∧ x 2 ∈ Set.Ioo (0 : ℝ) 1}, f (x 0) * ENNReal.ofReal ((x 2) ^ 2 * |inner ℝ (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) (v (x 0))|)) = (4 / 3 : ENNReal) * ∫⁻ s in S, f s * ENNReal.ofReal ‖v s‖ :=
  @proof_SphereGeom_Aux_Crofton_parameter_frame_weighted_lintegral
