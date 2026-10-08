import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_label_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.boundary_label_geometry :
    ∀ (D : Pt) (hD : D ∈ LamC)
    (hK : IsRegularRegionCrofton (SigmaD D)), MeasurableSet (arcA D) ∧ MeasurableSet (arcB D) ∧
      arcMeasure (arcA D ∩ arcB D) = 0 ∧ arcMeasure (arcA D) < ⊤ ∧
      arcMeasure (arcB D) < ⊤ :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_label_geometry
