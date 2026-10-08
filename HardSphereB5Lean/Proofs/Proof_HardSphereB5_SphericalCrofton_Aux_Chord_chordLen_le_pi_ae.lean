import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Chord_arcMeasure_greatCircle_closedHemisphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_chordLen_le_pi_ae {K : Set Pt} (hK : IsRegularRegionCrofton K) :
    ∀ᵐ p ∂dOmega, chordLen K (greatCircle p) ≤ π := by
  obtain ⟨n,hn,hH⟩ := hK.in_closed_hemisphere
  let m : Pt := ‖n‖⁻¹ • n
  have hnn : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hm : ‖m‖ = 1 := by
    simp [m, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg n), hnn]
  have hsub : K ⊆ {u : Pt | 0 ≤ inner ℝ m u} := by
    intro u hu
    change 0 ≤ inner ℝ m u
    dsimp [m]
    rw [real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg n)) (hH u hu)
  have hsingleton (x : Pt) : dOmega {x} = 0 := by
    have hh : dOmega ((fun u : Pt => inner ℝ m u) ⁻¹' {inner ℝ m x}) = 0 := by
      rw [← Measure.map_apply (by fun_prop : Measurable (fun u : Pt => inner ℝ m u))
        (measurableSet_singleton _), SphereGeom.dOmega_map_inner m hm]
      simp only [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton _)]
      have hz : (volume : Measure ℝ) ({inner ℝ m x} ∩ Set.Icc (-1) 1) = 0 :=
        measure_mono_null Set.inter_subset_left (measure_singleton _)
      rw [hz, smul_zero]
    exact measure_mono_null (by
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst u
      exact Set.mem_singleton _) hh
  have hunit : ∀ᵐ p ∂dOmega, ‖p‖ = 1 := by
    have hs : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0 : Pt) 1 :=
      ae_iff.mpr SphereGeom.dOmega_compl_sphere
    filter_upwards [hs] with p hp
    simpa [Metric.mem_sphere, dist_zero_right] using hp
  have hpm : ∀ᵐ p ∂dOmega, p ≠ m := by
    simpa [ae_iff] using hsingleton m
  have hpmm : ∀ᵐ p ∂dOmega, p ≠ -m := by
    simpa [ae_iff] using hsingleton (-m)
  filter_upwards [hunit,hpm,hpmm] with p hp hpn hpnm
  have hHlen := SphereGeom.Aux.Chord.arcMeasure_greatCircle_closedHemisphere m p hm hp hpn hpnm
  have hle : arcMeasure (greatCircle p ∩ K) ≤ ENNReal.ofReal π := by
    rw [← hHlen]
    exact measure_mono (by intro u hu; exact ⟨hu.1, hsub hu.2⟩)
  calc
    chordLen K (greatCircle p) = (arcMeasure (greatCircle p ∩ K)).toReal := rfl
    _ ≤ (ENNReal.ofReal π).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = π := ENNReal.toReal_ofReal Real.pi_pos.le
