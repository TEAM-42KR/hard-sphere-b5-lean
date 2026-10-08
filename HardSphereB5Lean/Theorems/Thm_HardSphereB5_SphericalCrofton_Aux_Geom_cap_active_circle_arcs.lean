import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_active_circle_arcs
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.cap_active_circle_arcs :
    ∀ (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m) (h1 : ∀ m, h m < 1) (j : Fin N), ∃ (M : ℕ) (γ : Fin M → ℝ → Pt) (F : Set Pt), F.Finite ∧
      (∀ m, ContDiff ℝ 2 (γ m)) ∧ (∀ m, Set.InjOn (γ m) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (γ m) t ≠ 0) ∧
      ((⋂ m, cap (n m) (h m)) ∩ {u : Pt | inner ℝ (n j) u = h j}) =
        (⋃ m, γ m '' Set.Icc (0 : ℝ) 1) ∪ F :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_active_circle_arcs
