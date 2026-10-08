import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_counted_jacobian_map
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.counted_jacobian_map :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → E) (f' : E → E →L[ℝ] E) (s H : Set E) (hf : Measurable f) (hs : MeasurableSet s) (hH : MeasurableSet H) (hm : Measurable f') (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hcount : ∀ᵐ y ∂μ, ({x : E | x ∈ s ∧ f x = y}.encard : ENNReal) = H.indicator (fun _ => (1 : ENNReal)) y), ((μ.restrict s).withDensity (fun x => ENNReal.ofReal |(f' x).det|)).map f = μ.restrict H :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_counted_jacobian_map
