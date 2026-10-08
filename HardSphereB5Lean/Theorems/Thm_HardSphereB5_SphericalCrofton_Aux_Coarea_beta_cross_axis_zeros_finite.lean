import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_beta_cross_axis_zeros_finite
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.MovingArc
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.beta_cross_axis_zeros_finite :
    ∀ (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) (hD1 : D 1 ≠ 0) (α : ℝ) (hα : Real.sin α ≠ 0), {β ∈ Set.Icc (-Real.pi) Real.pi | inner ℝ (SphereGeom.cross (u D α) (v D β)) e = 0}.Finite :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_beta_cross_axis_zeros_finite
