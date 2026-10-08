import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_swap
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.density_swap :
    ∀ (u v τ1 τ2 : Pt), santaloDens u v τ1 τ2 = santaloDens v u τ2 τ1 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_swap
