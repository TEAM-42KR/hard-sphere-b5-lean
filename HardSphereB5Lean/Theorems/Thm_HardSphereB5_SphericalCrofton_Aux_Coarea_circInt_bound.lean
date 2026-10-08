import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_circInt_bound
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.circInt_bound :
    ∀ (p p' : Pt) (hp : p ∈ FA) (hp' : p' ∈ FB) (hd0 : 0 < dist p p') (hd1 : dist p p' < 1), |circInt p p'| ≤ 2 * Real.pi * (dist p p') ^ 2 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_circInt_bound
