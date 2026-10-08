import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Arrangement_clipped_circle_arcs
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

theorem SphereGeom.Aux.Arrangement.clipped_circle_arcs :
    ∀ (k : ℕ) (c e1 e2 n : SphereGeom.E3) (hframe : Orthonormal ℝ ![e1,e2,n]) (r : ℝ) (hr : 0 < r) (α β δ : Fin k → ℝ),
    let S : Set SphereGeom.E3 := SphereGeom.circlePt c e1 e2 r '' {t ∈ Set.Icc 0 (2 * Real.pi) | ∀ i, 0 ≤ α i * Real.cos t + β i * Real.sin t - δ i}; ∃ (M : ℕ) (γ : Fin M → ℝ → SphereGeom.E3) (F : Set SphereGeom.E3), F.Finite ∧ (∀ m, ContDiff ℝ 2 (γ m)) ∧ (∀ m, Set.InjOn (γ m) (Set.Icc 0 1)) ∧ (∀ m, ∀ t ∈ Set.Icc 0 1, deriv (γ m) t ≠ 0) ∧ S = (⋃ m, γ m '' Set.Icc 0 1) ∪ F :=
  @proof_SphereGeom_Aux_Arrangement_clipped_circle_arcs
