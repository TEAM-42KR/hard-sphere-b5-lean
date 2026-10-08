import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_boundary_arcs
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.cap_boundary_arcs :
    ∀ (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty), ∃ (M : ℕ) (γ : Fin M → ℝ → Pt), (∀ m, ContDiff ℝ 2 (γ m)) ∧
      (∀ m, Set.InjOn (γ m) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (γ m) t ≠ 0) ∧
      sFrontier (⋂ m, cap (n m) (h m)) = ⋃ m, γ m '' Set.Icc (0 : ℝ) 1 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_boundary_arcs
