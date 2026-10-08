import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_coord_two_zeros_finite
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.endpoint_coord_two_zeros_finite :
    ∀ (D : Pt) (hD2 : D 2 ≠ 0), {α ∈ Set.Icc (-Real.pi) Real.pi | (D + u D α) 2 = 0}.Finite ∧
    {β ∈ Set.Icc (-Real.pi) Real.pi | (D + v D β) 2 = 0}.Finite :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_coord_two_zeros_finite
