import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_finite_arc_perimeter
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open MeasureTheory SphereGeom
open HardSphereB5.Lean (Pt)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.finite_arc_perimeter :
    ∀ (N : ℕ) (γ : Fin N → ℝ → Pt)
    (hγ : ∀ m, ContDiff ℝ 2 (γ m)), arcMeasure (⋃ m, γ m '' Set.Icc (0 : ℝ) 1) < ⊤ :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_finite_arc_perimeter
