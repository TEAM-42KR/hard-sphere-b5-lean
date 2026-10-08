import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_restrict_union_null
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.restrict_union_null :
    ∀ (μ : Measure Pt) (A B : Set Pt) (hB : MeasurableSet B) (hAB : μ (A ∩ B) = 0), μ.restrict (A ∪ B) = μ.restrict A + μ.restrict B :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_restrict_union_null
