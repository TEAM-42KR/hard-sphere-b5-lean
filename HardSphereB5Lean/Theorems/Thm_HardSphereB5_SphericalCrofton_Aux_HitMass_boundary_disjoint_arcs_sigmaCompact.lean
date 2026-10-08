import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_boundary_disjoint_arcs_sigmaCompact
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.boundary_disjoint_arcs_sigmaCompact :
    ∀ {K : Set Pt}
    (hK : IsRegularRegionCrofton K), ∃ (N : ℕ) (γ : Fin N → ℝ → Pt) (S : Fin N → Set ℝ),
      (∀ m, ContDiff ℝ 1 (γ m)) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖γ m t‖ = 1) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (γ m) t ≠ 0) ∧
      (∀ m, Set.InjOn (γ m) (Set.Icc 0 1)) ∧
      (∀ m, MeasurableSet (S m)) ∧
      (∀ m, S m ⊆ Set.Icc 0 1) ∧
      (∀ m, MeasurableSet (γ m '' S m)) ∧
      (Pairwise fun i j => Disjoint (γ i '' S i) (γ j '' S j)) ∧
      (∀ m, IsSigmaCompact (γ m '' S m)) ∧
      sFrontier K = ⋃ m, γ m '' S m :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_boundary_disjoint_arcs_sigmaCompact
