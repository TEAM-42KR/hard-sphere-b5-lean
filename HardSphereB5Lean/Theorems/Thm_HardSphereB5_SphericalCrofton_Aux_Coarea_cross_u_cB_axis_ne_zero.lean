import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_cross_u_cB_axis_ne_zero
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.MovingArc
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.cross_u_cB_axis_ne_zero :
    ∀ (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) (hD1 : D 1 ≠ 0) (α : ℝ) (hα : Real.sin α ≠ 0), inner ℝ (SphereGeom.cross (u D α) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)) e ≠ 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_cross_u_cB_axis_ne_zero
