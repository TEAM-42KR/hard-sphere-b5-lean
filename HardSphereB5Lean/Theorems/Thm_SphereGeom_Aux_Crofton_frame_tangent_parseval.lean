import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_frame_tangent_parseval
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.frame_tangent_parseval :
    ∀ (a b g v : E3) (hframe : Orthonormal ℝ ![a, b, g]) (hvg : inner ℝ v g = 0), (inner ℝ a v) ^ 2 + (inner ℝ b v) ^ 2 = ‖v‖ ^ 2 :=
  @proof_SphereGeom_Aux_Crofton_frame_tangent_parseval
