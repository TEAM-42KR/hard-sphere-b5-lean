import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_monotone_eq_measure_on_measurable_of_sigmaCompact
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.monotone_eq_measure_on_measurable_of_sigmaCompact :
    ∀ (F : Set ℝ → ENNReal) (hF : Monotone F) (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) (hEq : ∀ T : Set ℝ, T ⊆ Set.Icc a b → IsSigmaCompact T → F T = ν T) (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b), F S = ν S :=
  @proof_SphereGeom_Aux_Crofton_monotone_eq_measure_on_measurable_of_sigmaCompact
