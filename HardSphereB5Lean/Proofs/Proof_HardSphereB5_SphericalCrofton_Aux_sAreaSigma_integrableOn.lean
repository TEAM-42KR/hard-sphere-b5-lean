import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_measurable
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_integrableOn : IntegrableOn (fun D : Pt => sArea (SigmaD D)) LamC := by
  have hfinite : volume LamC ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono (show LamC ⊆ Metric.closedBall (0 : Pt) 1 from Set.inter_subset_left))
      (measure_closedBall_lt_top (μ := volume) (x := (0 : Pt)) (r := 1))
  apply Measure.integrableOn_of_bounded hfinite Aux.sAreaSigma_measurable.aestronglyMeasurable
  filter_upwards [] with D
  rw [Real.norm_eq_abs, abs_of_nonneg (Aux.sAreaSigma_bound D).1]
  exact (Aux.sAreaSigma_bound D).2

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_integrableOn
