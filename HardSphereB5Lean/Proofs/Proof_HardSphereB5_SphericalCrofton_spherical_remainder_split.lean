import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_pole_transport
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_chord_law_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_label_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_kernel_partition
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_terms
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Sigma_regular_or_small
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_empty_patch
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_singleton_patch
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_spherical_remainder_split (f : Kern) (D : Pt) (hD : D ∈ LamC) :
    Rf f (SigmaD D) = AAf f D + BBf f D + ABf f D := by
  rcases HardSphereB5.SphericalCrofton.Aux.Sigma_regular_or_small D hD with hK | hsmall
  · obtain ⟨hKm,hAm,hBm,hpm,hdm,hdpos⟩ := pair_measurable D
    obtain ⟨hAm',hBm',hAB,hAf,hBf⟩ := boundary_label_geometry D hD hK
    let g : Pt → ℝ := fun p => if 0 < chordLen (SigmaD D) (greatCircle p) ∧
      chordLen (SigmaD D) (greatCircle p) < π/3 then phiK f (chordLen (SigmaD D) (greatCircle p)) else 0
    let c : Pt×Pt → ℝ := fun q => cutKern f (pairDelta q)
    have hgi : Integrable g dOmega := (HardSphereB5.SphericalCrofton.Aux.Chord.integrable_terms (SigmaD D) hKm f).2.2.1
    have ht := pair_pole_transport D hD hK
    have hgm : Integrable g ((weightedPairMu D).map pairPole) := by
      rw [ht]
      exact hgi.restrict
    have hcEq : (g ∘ pairPole) =ᵐ[weightedPairMu D] c := by
      filter_upwards [pair_chord_law_ae D hD hK] with q hq
      dsimp [Function.comp_def,g,c]
      rw [hq.2]
      simp only [hq.1, true_and, cutKern]
    have hci : Integrable c (weightedPairMu D) :=
      (hgm.comp_aemeasurable hpm.aemeasurable).congr hcEq
    have hwMeas : Measurable (fun q => ENNReal.ofReal (pairDens D q)) := hdm.ennreal_ofReal
    have hwFin : ∀ᵐ q ∂pairMu D, ENNReal.ofReal (pairDens D q) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hpairEq : (fun q => c q * (ENNReal.ofReal (pairDens D q)).toReal) = pairKernel f D := by
      funext q
      rw [ENNReal.toReal_ofReal (hdpos q)]
      rfl
    have hpairInt : Integrable (pairKernel f D) (pairMu D) := by
      have hi := (integrable_withDensity_iff hwMeas hwFin).mp hci
      rwa [hpairEq] at hi
    have hI : (∫ p, g p ∂dOmega) = ∫ q, pairKernel f D q ∂pairMu D := by
      have hgSupport : (∫ p in hitPoleSet D, g p ∂dOmega) = ∫ p, g p ∂dOmega := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro p hp
        have hnot : ¬ 0 < chordLen (SigmaD D) (greatCircle p) := hp
        simp [g,hnot]
      calc
        (∫ p, g p ∂dOmega) = ∫ p in hitPoleSet D, g p ∂dOmega := hgSupport.symm
        _ = ∫ p, g p ∂(weightedPairMu D).map pairPole := by rw [ht]
        _ = ∫ q, g (pairPole q) ∂weightedPairMu D :=
          integral_map hpm.aemeasurable hgm.aestronglyMeasurable
        _ = ∫ q, c q ∂weightedPairMu D := integral_congr_ae hcEq
        _ = ∫ q, (ENNReal.ofReal (pairDens D q)).toReal • c q ∂pairMu D :=
          integral_withDensity_eq_integral_toReal_smul hwMeas hwFin c
        _ = ∫ q, pairKernel f D q ∂pairMu D := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun q => by
            dsimp only
            rw [ENNReal.toReal_ofReal (hdpos q)]
            simp only [smul_eq_mul, pairKernel, c]
            ring
    have hpart := boundary_kernel_partition f D hAm hBm hAB hAf hBf hpairInt
    change (1/2:ℝ) * (∫ p, g p ∂dOmega) = _
    rw [hI]
    simpa only using hpart
  · rcases (SigmaD D).eq_empty_or_nonempty with hemp | ⟨V,hV⟩
    · exact empty_patch f D hemp
    · exact singleton_patch f D V (hsmall.eq_singleton_of_mem hV)
