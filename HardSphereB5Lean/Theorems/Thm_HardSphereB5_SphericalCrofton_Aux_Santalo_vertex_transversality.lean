import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_vertex_transversality
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.vertex_transversality :
    ∀ (D w : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) (hw : w ∈ vertsD D), cross (cross (nAv D) w) (cross (nBv D) w) ≠ 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_vertex_transversality
