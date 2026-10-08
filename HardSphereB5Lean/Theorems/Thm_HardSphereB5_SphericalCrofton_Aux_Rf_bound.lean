import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Rf_bound
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Rf_bound :
    ∀ (f : Kern) (K : Set Pt), 0 ≤ Rf f K ∧ Rf f K ≤ 12 * π :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Rf_bound
