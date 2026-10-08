import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_definition_chain
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.definition_chain :
    ∀ (f : Kern), Jnear f = ECr f + Rsame f + ABint f :=
  @proof_HardSphereB5_SphericalCrofton_definition_chain
