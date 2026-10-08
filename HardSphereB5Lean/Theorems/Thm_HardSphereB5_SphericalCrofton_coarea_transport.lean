import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_coarea_transport
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.coarea_transport :
    ∀ (f : Kern), frakB f = ∫ p in FA, ∫ p' in FB,
      (if 0 < dist p p' ∧ dist p p' < 1 then
          rhoK f (1 - dist p p' ^ 2 / 2) / dist p p' * circInt p p' else 0)
        ∂(sphereMeasure e) ∂(sphereMeasure 0) :=
  @proof_HardSphereB5_SphericalCrofton_coarea_transport
