import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_sigmaCompact
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.measurable_encard_greatCircle_sigmaCompact :
    ∀ (A : Set E3) (hA : IsSigmaCompact A), Measurable (fun p : E3 => ((greatCircle p ∩ A).encard : ENNReal)) :=
  @proof_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_sigmaCompact
