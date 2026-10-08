import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_boundary_disjoint_arcs_sigmaCompact
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_encard_off_support
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_sigmaCompact
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_lintegral_encard_greatCircle_image
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ArcLength_arcMeasure_image_regular
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SupportCircles_support_poles_null
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_bounded_comp
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 1200000

theorem proof_HardSphereB5_SphericalCrofton_hit_mass {K : Set Pt} (hK : IsRegularRegionCrofton K) :
    gcIntegral (fun G => if 0 < chordLen K G then 1 else 0) = perim K := by
  classical
  obtain ⟨N, γ, S, hγ, hsphere, hreg, hinj, hS, hSI, hImg, hdisj, hSigma, hcover⟩ :=
    HardSphereB5.SphericalCrofton.Aux.HitMass.boundary_disjoint_arcs_sigmaCompact hK
  have hcount (p : Pt) : ((greatCircle p ∩ sFrontier K).encard : ENNReal) =
      ∑ m, ((greatCircle p ∩ γ m '' S m).encard : ENNReal) := by
    rw [hcover, Set.inter_iUnion]
    have hd : Pairwise fun i j =>
        Disjoint (greatCircle p ∩ γ i '' S i) (greatCircle p ∩ γ j '' S j) := by
      intro i j hij
      exact (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
    rw [Set.encard_iUnion_of_finite hd, finsum_eq_sum_of_fintype]
    change ENat.toENNRealRingHom (∑ m, (greatCircle p ∩ γ m '' S m).encard) =
      ∑ m, ENat.toENNRealRingHom ((greatCircle p ∩ γ m '' S m).encard)
    exact map_sum ENat.toENNRealRingHom _ _
  have hboundary : (∫⁻ p, ((greatCircle p ∩ sFrontier K).encard : ENNReal) ∂dOmega) =
      4 * arcMeasure (sFrontier K) := by
    calc
      _ = ∫⁻ p, ∑ m, ((greatCircle p ∩ γ m '' S m).encard : ENNReal) ∂dOmega :=
        lintegral_congr_ae (Filter.Eventually.of_forall hcount)
      _ = ∑ m, ∫⁻ p, ((greatCircle p ∩ γ m '' S m).encard : ENNReal) ∂dOmega := by
        exact lintegral_finsetSum' Finset.univ (fun m _ =>
          (SphereGeom.Aux.Crofton.measurable_encard_greatCircle_sigmaCompact
            (γ m '' S m) (hSigma m)).aemeasurable)
      _ = ∑ m, 4 * arcMeasure (γ m '' S m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [SphereGeom.Aux.Crofton.lintegral_encard_greatCircle_image
          (γ m) 0 1 (hγ m) (hsphere m) (hreg m) (hinj m) (S m) (hS m) (hSI m),
          SphereGeom.Aux.ArcLength.arcMeasure_image_regular
          (γ m) 0 1 (hγ m) (hreg m) (hinj m) (S m) (hS m) (hSI m)]
      _ = 4 * ∑ m, arcMeasure (γ m '' S m) := by rw [Finset.mul_sum]
      _ = 4 * arcMeasure (sFrontier K) := by
        congr 1
        rw [hcover]
        symm
        simpa using measure_biUnion_finset (μ := arcMeasure) (s := Finset.univ)
          (fun i _ j _ hij => hdisj hij) (fun m _ => hImg m)
  let H : Pt → ℝ := fun p => if 0 < chordLen K (greatCircle p) then 1 else 0
  have hInt : Integrable H dOmega := by
    refine HardSphereB5.SphericalCrofton.Aux.Chord.integrable_bounded_comp K hK.isCompact.measurableSet
      (fun x : ℝ => if 0 < x then 1 else 0) ?_ 1 ?_
    · exact measurable_const.ite measurableSet_Ioi measurable_const
    · intro x hx
      split_ifs <;> norm_num
  have hnonneg : ∀ p, 0 ≤ H p := by intro p; dsimp [H]; split_ifs <;> norm_num
  have hsn : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0 : Pt) 1 := by
    exact ae_iff.mpr SphereGeom.dOmega_compl_sphere
  have hsupport := SphereGeom.Aux.SupportCircles.support_poles_null K hK.subset_sphere
  have hnot : ∀ᵐ p ∂dOmega, p ∉ {p : Pt | ‖p‖ = 1 ∧
      ((∀ u ∈ K, inner ℝ p u ≤ 0) ∨ (∀ u ∈ K, 0 ≤ inner ℝ p u)) ∧
        ∃ u ∈ K, inner ℝ p u = 0} := by
    exact ae_iff.mpr (by simpa only [Set.mem_setOf_eq, not_not] using hsupport)
  have hae : (fun p => ((greatCircle p ∩ sFrontier K).encard : ENNReal)) =ᵐ[dOmega]
      (fun p => (2 : ENNReal) * ENNReal.ofReal (H p)) := by
    filter_upwards [hsn, hnot] with p hp hn
    have hp' : ‖p‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp
    have hn' : ¬ (((∀ u ∈ K, inner ℝ p u ≤ 0) ∨ (∀ u ∈ K, 0 ≤ inner ℝ p u)) ∧
        ∃ u ∈ K, inner ℝ p u = 0) := fun h => hn ⟨hp', h⟩
    rw [HardSphereB5.SphericalCrofton.Aux.HitMass.encard_off_support hK p hp' hn']
    dsimp [H]
    split_ifs <;> norm_num
  have hreal : (2 : ENNReal) * ENNReal.ofReal (∫ p, H p ∂dOmega) =
      4 * arcMeasure (sFrontier K) := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall hnonneg)]
    rw [← lintegral_const_mul' (2 : ENNReal) _ (by norm_num)]
    rw [← lintegral_congr_ae hae]
    exact hboundary
  have hi0 : 0 ≤ ∫ p, H p ∂dOmega := integral_nonneg hnonneg
  have hr := congrArg ENNReal.toReal hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hi0] at hr
  change (1 / 2 : ℝ) * (∫ p, H p ∂dOmega) = (arcMeasure (sFrontier K)).toReal
  linarith
