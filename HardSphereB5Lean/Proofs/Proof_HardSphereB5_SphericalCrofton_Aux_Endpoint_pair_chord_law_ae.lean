import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_transverse_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_chordLen_eq_delta_of_boundary_pair
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_crossing_boundary_pair
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_chord_law_ae (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) :
    ∀ᵐ q ∂weightedPairMu D, 0 < pairDelta q ∧
      chordLen (SigmaD D) (greatCircle (pairPole q)) = pairDelta q := by
  filter_upwards [pair_transverse_ae D hD hK] with q hq
  obtain ⟨hp,hneq,hu,hv,hneg,hpos⟩ := hq
  obtain ⟨a,b,hab,hbd,hL⟩ := HardSphereB5.SphericalCrofton.Aux.HitMass.crossing_boundary_pair
    hK (pairPole q) hp hneg hpos
  have hu' : q.1=a ∨ q.1=b := by
    rw [hbd] at hu
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hu
  have hv' : q.2=a ∨ q.2=b := by
    rw [hbd] at hv
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hv
  have hb : greatCircle (pairPole q) ∩ sFrontier (SigmaD D) = {q.1,q.2} := by
    rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact False.elim (hneq (hu'.trans hv'.symm))
    · simpa only [hu',hv'] using hbd
    · simpa only [hu',hv',Set.pair_comm] using hbd
    · exact False.elim (hneq (hu'.trans hv'.symm))
  exact chordLen_eq_delta_of_boundary_pair hK (pairPole q) q.1 q.2 hp hneq hb hL
