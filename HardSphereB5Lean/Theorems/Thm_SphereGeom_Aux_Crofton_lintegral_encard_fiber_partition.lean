import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_lintegral_encard_fiber_partition
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.lintegral_encard_fiber_partition :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → E) (f' : E → E →L[ℝ] E) (s : ℕ → Set E) (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hf' : ∀ n x, x ∈ s n → HasFDerivWithinAt f (f' x) (s n) x) (hinj : ∀ n, Set.InjOn f (s n)), (∫⁻ y, ({x : E | x ∈ ⋃ n, s n ∧ f x = y}.encard : ENNReal) ∂μ) = ∫⁻ x in ⋃ n, s n, ENNReal.ofReal |(f' x).det| ∂μ :=
  @proof_SphereGeom_Aux_Crofton_lintegral_encard_fiber_partition
