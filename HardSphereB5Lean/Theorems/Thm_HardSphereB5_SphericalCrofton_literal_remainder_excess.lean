import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_literal_remainder_excess
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.literal_remainder_excess :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), RfAll f K = Rf f K + bK f * (2 * π - perim K) :=
  @proof_HardSphereB5_SphericalCrofton_literal_remainder_excess
