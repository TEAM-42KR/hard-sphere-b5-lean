import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_interior_transport
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.regular_cone_interior_transport :
    ∀ (K : Set Pt),
    let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}; ∀ u : Pt, ‖u‖ = 1 → (u ∈ interior C ↔ u ∈ sInterior K) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_interior_transport
