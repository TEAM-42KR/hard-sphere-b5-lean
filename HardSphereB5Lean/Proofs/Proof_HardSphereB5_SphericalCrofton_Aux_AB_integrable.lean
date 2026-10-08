import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_spherical_remainder_split
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Rf_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_AAf_nonneg
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_BBf_nonneg
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_ABf_nonneg
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_ABf_aestronglyMeasurable
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_AB_integrable (f : Kern) : IntegrableOn (ABf f) LamC := by
  have hfinite : volume LamC ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono (show LamC ⊆ Metric.closedBall (0 : Pt) 1 from Set.inter_subset_left))
      (measure_closedBall_lt_top (μ := volume) (x := (0 : Pt)) (r := 1))
  have hLam : MeasurableSet LamC := (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).measurableSet
  letI : IsFiniteMeasure (volume.restrict LamC) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (lt_top_iff_ne_top.mpr hfinite)⟩
  apply (integrable_const (12 * Real.pi : ℝ)).mono' (Aux.ABf_aestronglyMeasurable f)
  filter_upwards [ae_restrict_mem hLam] with D hD
  rw [Real.norm_eq_abs, abs_of_nonneg (Aux.ABf_nonneg f D)]
  have hs := spherical_remainder_split f D hD
  have hb := (Aux.Rf_bound f (SigmaD D)).2
  linarith [Aux.AAf_nonneg f D, Aux.BBf_nonneg f D]
