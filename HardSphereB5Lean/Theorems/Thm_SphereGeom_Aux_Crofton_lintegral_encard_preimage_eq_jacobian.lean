import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_lintegral_encard_preimage_eq_jacobian
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.lintegral_encard_preimage_eq_jacobian :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → E) (f' : E → E →L[ℝ] E) (s : Set E) (hs : MeasurableSet s) (hm : Measurable f') (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x), (∫⁻ y, ({x : E | x ∈ s ∧ f x = y}.encard : ENNReal) ∂μ) = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ :=
  @proof_SphereGeom_Aux_Crofton_lintegral_encard_preimage_eq_jacobian
