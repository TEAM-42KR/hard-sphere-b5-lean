import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_empty_patch
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.empty_patch :
    ∀ (f : Kern) (D : Pt) (hK : SigmaD D = ∅), Rf f (SigmaD D) = AAf f D + BBf f D + ABf f D :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_empty_patch
