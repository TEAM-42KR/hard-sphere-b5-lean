import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_exists_injective_partition_regular
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.Crofton.exists_injective_partition_regular :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f : E → E) (f' : E → E →L[ℝ] E) (s : Set E) (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hreg : ∀ x ∈ s, (f' x).det ≠ 0), ∃ t : ℕ → Set E, (∀ n, MeasurableSet (t n)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧ (⋃ n, t n) = s ∧ (∀ n, Set.InjOn f (t n)) ∧ (∀ n, t n ⊆ s) :=
  @proof_SphereGeom_Aux_Crofton_exists_injective_partition_regular
