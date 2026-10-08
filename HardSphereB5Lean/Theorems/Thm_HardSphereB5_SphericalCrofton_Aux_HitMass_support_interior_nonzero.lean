import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_support_interior_nonzero
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.support_interior_nonzero :
    ∀ (C : Set Pt) (n : Pt) (hn : n ≠ 0)
    (hs : ∀ v ∈ C, 0 ≤ inner ℝ n v) {v : Pt} (hv : v ∈ interior C), v ≠ 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_support_interior_nonzero
