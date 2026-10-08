import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_crofton_decomposition
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.crofton_decomposition :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), Ff f K = cA f * sArea K - cP f * perim K + Rf f K :=
  @proof_HardSphereB5_SphericalCrofton_crofton_decomposition
