import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_kernel_integrable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.kernel_integrable :
    ∀ (f : Kern), Integrable (Function.uncurry (fun p p' : Pt =>
    if 0 < dist p p' ∧ dist p p' < 1 then
      rhoK f (1 - dist p p' ^ 2 / 2) / dist p p' * circInt p p' else 0))
    (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_kernel_integrable
