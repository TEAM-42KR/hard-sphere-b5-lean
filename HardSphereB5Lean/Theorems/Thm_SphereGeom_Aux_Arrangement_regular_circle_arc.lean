import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Arrangement_regular_circle_arc
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

theorem SphereGeom.Aux.Arrangement.regular_circle_arc :
    ∀ (c e1 e2 n : SphereGeom.E3) (hframe : Orthonormal ℝ ![e1,e2,n]) (r a b : ℝ) (hr : 0 < r) (hab : a < b) (hshort : b - a < 2 * Real.pi),
    let γ : ℝ → SphereGeom.E3 := fun t => SphereGeom.circlePt c e1 e2 r (a + (b - a) * t); ContDiff ℝ 2 γ ∧ Set.InjOn γ (Set.Icc 0 1) ∧ (∀ t, deriv γ t ≠ 0) ∧ γ '' Set.Icc 0 1 = SphereGeom.circlePt c e1 e2 r '' Set.Icc a b :=
  @proof_SphereGeom_Aux_Arrangement_regular_circle_arc
