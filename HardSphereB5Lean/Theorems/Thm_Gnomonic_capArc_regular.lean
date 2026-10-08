import HardSphereB5Lean.Proofs.Proof_Gnomonic_capArc_regular
import HardSphereB5Lean.Definitions.Def_Gnomonic_CapFrame
set_option autoImplicit false
open SphereGeom Gnomonic
open scoped RealInnerProductSpace

theorem Gnomonic.capArc_regular :
    ∀ (n a e1 e2 : E3) (h : ℝ)
    (F : CapFrame a e1 e2) (hh : |h| < 1) (hn : ⟪n, n⟫ = 1), IsOpen (visible n a e1 e2 h) ∧
    ContDiffOn ℝ 2 (projectedArc n a e1 e2 h) (visible n a e1 e2 h) ∧
    ∀ t ∈ visible n a e1 e2 h,
      ⟪projectedArc n a e1 e2 h t, n⟫ = 0 ∧
      ContDiffAt ℝ 2 (projectedArc n a e1 e2 h) t ∧
      HasDerivAt (projectedArc n a e1 e2 h)
        (projectVelocity n (capArc a e1 e2 h t) (capVelocity e1 e2 h t)) t ∧
      projectVelocity n (capArc a e1 e2 h t) (capVelocity e1 e2 h t) ≠ 0 :=
  @proof_Gnomonic_capArc_regular
