import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_dOmega_greatCircle_eq_zero
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_ae_encard_image_diff_countable (γ : ℝ → E3) (S T : Set ℝ) (hT : T.Countable)
    (hs : ∀ s ∈ S, ‖γ s‖ = 1) :
    (fun p : E3 => ((greatCircle p ∩ γ '' (S \ T)).encard : ENNReal)) =ᵐ[dOmega]
      (fun p : E3 => ((greatCircle p ∩ γ '' S).encard : ENNReal)) := by
  have hA : (γ '' (S ∩ T)).Countable := (hT.mono Set.inter_subset_right).image γ
  have hp : ∀ᵐ p ∂dOmega, ‖p‖ = 1 := by
    rw [ae_iff]
    simpa [Metric.sphere, dist_zero_right, Set.compl_setOf] using dOmega_compl_sphere
  have hav : ∀ᵐ p ∂dOmega, ∀ x ∈ γ '' (S ∩ T), p ∉ greatCircle x := by
    rw [ae_ball_iff hA]
    intro x hx
    obtain ⟨s, hst, rfl⟩ := hx
    rw [ae_iff]
    simpa using SphereGeom.Aux.Crofton.dOmega_greatCircle_eq_zero (γ s) (hs s hst.1)
  filter_upwards [hp, hav] with p hpn havoid
  have he : greatCircle p ∩ γ '' (S \ T) = greatCircle p ∩ γ '' S := by
    apply Set.Subset.antisymm
    · exact Set.inter_subset_inter_right _ (Set.image_mono Set.diff_subset)
    · rintro x ⟨hx, s, hss, rfl⟩
      refine ⟨hx, s, ⟨hss, ?_⟩, rfl⟩
      intro hst
      exact havoid (γ s) ⟨s, ⟨hss, hst⟩, rfl⟩
        ⟨hpn, by simpa only [real_inner_comm] using hx.2⟩
  rw [he]
