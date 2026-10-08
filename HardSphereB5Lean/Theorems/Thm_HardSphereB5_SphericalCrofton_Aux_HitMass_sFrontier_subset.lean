import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_sFrontier_subset
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.sFrontier_subset :
    ∀ {K : Set Pt}
    (hK : IsClosed K), sFrontier K ⊆ K :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_sFrontier_subset
