import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Sigma_regular_or_small
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Sigma_regular_or_small :
    ∀ (D : Pt) (hD : D ∈ LamC), IsRegularRegionCrofton (SigmaD D) ∨ (SigmaD D).Subsingleton :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Sigma_regular_or_small
