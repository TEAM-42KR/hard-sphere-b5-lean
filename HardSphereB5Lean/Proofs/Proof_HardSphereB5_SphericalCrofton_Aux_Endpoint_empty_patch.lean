import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_empty_patch (f : Kern) (D : Pt) (hK : SigmaD D = ∅) : Rf f (SigmaD D) = AAf f D + BBf f D + ABf f D := by
  have ha : arcA D = ∅ := by simp [arcA, hK]
  have hb : arcB D = ∅ := by simp [arcB, hK]
  simp [AAf, BBf, ABf, ha, hb, hK, Rf, chordLen, len, gcIntegral]
