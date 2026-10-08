import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Chord_measurable_arcMeasure_greatCircle_inter
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Chord_arcMeasure_greatCircle_inter_le
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_bounded_comp (K : Set Pt) (hK : MeasurableSet K)
    (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π), ‖g x‖ ≤ B) :
    Integrable (fun p : Pt => g (chordLen K (greatCircle p))) dOmega := by
  haveI : IsFiniteMeasure dOmega := ⟨by
    rw [dOmega, SphereGeom.sphereMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  have hm : Measurable (fun p : Pt => chordLen K (greatCircle p)) := by
    exact (SphereGeom.Aux.Chord.measurable_arcMeasure_greatCircle_inter K hK).ennreal_toReal
  have hs : ∀ᵐ p ∂dOmega, ‖p‖ = 1 := by
    have hh : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0 : Pt) 1 := ae_iff.mpr SphereGeom.dOmega_compl_sphere
    filter_upwards [hh] with p hp
    simpa [Metric.mem_sphere, dist_eq_norm] using hp
  apply (integrable_const B).mono' (hg.comp hm).aestronglyMeasurable
  filter_upwards [hs] with p hp
  apply hB
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  change (arcMeasure (greatCircle p ∩ K)).toReal ≤ 2 * π
  have hbound := SphereGeom.Aux.Chord.arcMeasure_greatCircle_inter_le p hp K
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * π)] using hh
