import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false

open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

namespace HardSphereB5.SphericalCrofton.Aux.Coarea

def targetRegular (y : Chart5) : Prop :=
  let D := targetCenter y
  let p := targetEndpointA y
  let p' := targetEndpointB y
  p ∈ FA ∧ p' ∈ FB ∧ |y 0| < 1 ∧ |y 2| < 1 ∧
    y 1 ∈ Set.Ioo (-Real.pi) Real.pi ∧
    y 3 ∈ Set.Ioo (-Real.pi) Real.pi ∧
    y 4 ∈ Set.Ioo (-Real.pi) Real.pi ∧
    0 < dist p p' ∧ dist p p' < 1 ∧
    D ∈ LamC ∧ offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1 ∧
    centerFrame0 (p'-p) ≠ 0 ∧
    sourcePhaseA D p ∈ Complex.slitPlane ∧
    sourcePhaseB D p' ∈ Complex.slitPlane

end HardSphereB5.SphericalCrofton.Aux.Coarea
