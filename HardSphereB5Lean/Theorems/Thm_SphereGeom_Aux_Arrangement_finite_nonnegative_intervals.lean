import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Arrangement_finite_nonnegative_intervals
import Mathlib
set_option autoImplicit false

theorem SphereGeom.Aux.Arrangement.finite_nonnegative_intervals :
    ∀ (k : ℕ) (f : Fin k → ℝ → ℝ) (p q : ℝ) (hpq : p ≤ q) (hf : ∀ i, Continuous (f i)) (hz : ∀ i, ({t : ℝ | t ∈ Set.Icc p q ∧ f i t = 0}.Finite ∨ ∀ t, f i t = 0)), ∃ (M : ℕ) (a b : Fin M → ℝ) (F : Set ℝ), F.Finite ∧ (∀ m, a m < b m) ∧ {t : ℝ | t ∈ Set.Icc p q ∧ ∀ i, 0 ≤ f i t} = (⋃ m, Set.Icc (a m) (b m)) ∪ F :=
  @proof_SphereGeom_Aux_Arrangement_finite_nonnegative_intervals
