import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.pair_measurable :
    ∀ (D : Pt), MeasurableSet (SigmaD D) ∧ MeasurableSet (arcA D) ∧ MeasurableSet (arcB D) ∧ Measurable pairPole ∧ Measurable (pairDens D) ∧ (∀ q, 0 ≤ pairDens D q) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable
