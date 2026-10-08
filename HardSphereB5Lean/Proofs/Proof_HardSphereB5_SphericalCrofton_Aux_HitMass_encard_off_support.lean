import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_sFrontier_subset
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_crossing_boundary_pair
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_encard_off_support {K : Set Pt}
    (hK : IsRegularRegionCrofton K) (p : Pt) (hp : ‖p‖ = 1)
    (hns : ¬ (((∀ u ∈ K, inner ℝ p u ≤ 0) ∨ (∀ u ∈ K, 0 ≤ inner ℝ p u)) ∧
      ∃ u ∈ K, inner ℝ p u = 0)) :
    ((greatCircle p ∩ sFrontier K).encard : ENNReal) =
      if 0 < chordLen K (greatCircle p) then 2 else 0 := by
  classical
  by_cases hmeet : ∃ u ∈ K, inner ℝ p u = 0
  · have hpos : ∃ u ∈ K, 0 < inner ℝ p u := by
      by_contra hn
      apply hns
      exact ⟨Or.inl (fun u hu => le_of_not_gt (fun h => hn ⟨u, hu, h⟩)), hmeet⟩
    have hneg : ∃ u ∈ K, inner ℝ p u < 0 := by
      by_contra hn
      apply hns
      exact ⟨Or.inr (fun u hu => le_of_not_gt (fun h => hn ⟨u, hu, h⟩)), hmeet⟩
    obtain ⟨a, b, hab, hboundary, hlen⟩ :=
      HardSphereB5.SphericalCrofton.Aux.HitMass.crossing_boundary_pair hK p hp hneg hpos
    simp [hboundary, Set.encard_pair hab, hlen]
  · have hempty : greatCircle p ∩ K = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro u ⟨hu, hKu⟩
      exact hmeet ⟨u, hKu, hu.2⟩
    have hfront : greatCircle p ∩ sFrontier K = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro u ⟨hu, hFu⟩
      exact hmeet ⟨u, HardSphereB5.SphericalCrofton.Aux.HitMass.sFrontier_subset hK.isCompact.isClosed hFu, hu.2⟩
    simp [hfront, chordLen, len, hempty]
