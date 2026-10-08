import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_encard_off_support
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.encard_off_support :
    ∀ {K : Set Pt}
    (hK : IsRegularRegionCrofton K) (p : Pt) (hp : ‖p‖ = 1)
    (hns : ¬ (((∀ u ∈ K, inner ℝ p u ≤ 0) ∨ (∀ u ∈ K, 0 ≤ inner ℝ p u)) ∧
      ∃ u ∈ K, inner ℝ p u = 0)), ((greatCircle p ∩ sFrontier K).encard : ENNReal) =
      if 0 < chordLen K (greatCircle p) then 2 else 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_encard_off_support
