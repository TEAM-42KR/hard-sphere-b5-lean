import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_CapIntersection_basic_properties
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom MeasureTheory

theorem SphereGeom.Aux.CapIntersection.basic_properties :
    ∀ (N : ℕ) (hN : 0 < N) (n : Fin N → E3) (h : Fin N → ℝ) (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m), (⋂ m, cap (n m) (h m)) ⊆ Metric.sphere (0 : E3) 1 ∧ IsCompact (⋂ m, cap (n m) (h m)) ∧ (∃ z : E3, z ≠ 0 ∧ ∀ u ∈ ⋂ m, cap (n m) (h m), 0 ≤ inner ℝ z u) ∧ (∀ u ∈ ⋂ m, cap (n m) (h m), ∀ v ∈ ⋂ m, cap (n m) (h m), u ≠ -v → ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 - t) • u + t • v‖⁻¹ • ((1 - t) • u + t • v) ∈ ⋂ m, cap (n m) (h m)) :=
  @proof_SphereGeom_Aux_CapIntersection_basic_properties
