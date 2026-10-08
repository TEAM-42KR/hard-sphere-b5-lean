import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.B_chart_geometry :
    ∀ (D : Pt)
  (hL : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1), Orthonormal ℝ (EB D) ∧ 0 < HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D ∧
  0 < halfB D ∧ halfB D ≤ Real.pi ∧
  arcB D = HardSphereB5.SphericalCrofton.Aux.MovingArc.v D '' Set.Icc (-(halfB D)) (halfB D) ∧
  ∀ t : ℝ, HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D)
    (-cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t)) t :=
  @proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
