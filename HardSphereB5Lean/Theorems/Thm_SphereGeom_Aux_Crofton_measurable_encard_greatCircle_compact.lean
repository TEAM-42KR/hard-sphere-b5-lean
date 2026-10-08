import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_compact
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Classical

theorem SphereGeom.Aux.Crofton.measurable_encard_greatCircle_compact :
    ∀ (K : Set E3) (hK : IsCompact K), Measurable (fun p : E3 => ((greatCircle p ∩ K).encard : ENNReal)) :=
  @proof_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_compact
