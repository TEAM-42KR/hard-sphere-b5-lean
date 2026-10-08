import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_fixedZFrame_oriented_orthonormal
import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.fixedZFrame_oriented_orthonormal :
    ∀ (p : E3) (hp : ‖p‖ = 1) (hQ : p 0 ^ 2 + p 1 ^ 2 ≠ 0), Orthonormal ℝ ![fixedZA p, fixedZB p, p] ∧ SphereGeom.cross (fixedZA p) (fixedZB p) = p :=
  @proof_SphereGeom_Aux_Crofton_fixedZFrame_oriented_orthonormal
