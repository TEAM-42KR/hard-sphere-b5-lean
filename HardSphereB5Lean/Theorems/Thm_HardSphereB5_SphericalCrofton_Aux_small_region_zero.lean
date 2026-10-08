import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_small_region_zero
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.small_region_zero :
    ∀ (K : Set Pt) (hK : K.Subsingleton) (f : Kern), Ff f K = 0 ∧ sArea K = 0 ∧ perim K = 0 ∧ Rf f K = 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_small_region_zero
