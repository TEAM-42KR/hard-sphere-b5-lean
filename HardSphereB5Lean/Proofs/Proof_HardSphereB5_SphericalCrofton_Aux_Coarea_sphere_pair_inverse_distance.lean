import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_inverse_distance
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open scoped ENNReal
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_pair_inverse_distance :
    Integrable (fun pq : Pt × Pt => (dist pq.1 pq.2)⁻¹)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)) := by
  let μ := (sphereMeasure 0).restrict FA
  let ν := (sphereMeasure e).restrict FB
  haveI (c : Pt) : IsFiniteMeasure (sphereMeasure c) := ⟨by
    rw [sphereMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  have hFA : MeasurableSet FA := Metric.isClosed_sphere.measurableSet.inter measurableSet_closedBall
  have hm : Measurable (fun pq : Pt × Pt => (dist pq.1 pq.2)⁻¹) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem hFA] with p hp
    have hnp : ‖p-e‖ ≤ 1 := by simpa [dist_eq_norm] using hp.2
    exact (sphere_inverse_distance e p hnp).1.integrableOn
  · have hφ : AEStronglyMeasurable (fun p => ∫ q : Pt, ‖(dist p q)⁻¹‖ ∂ν) μ :=
      hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    refine (integrable_const (4*π : ℝ)).mono' hφ ?_
    filter_upwards [ae_restrict_mem hFA] with p hp
    have hnp : ‖p-e‖ ≤ 1 := by simpa [dist_eq_norm] using hp.2
    rcases sphere_inverse_distance e p hnp with ⟨hi,heq⟩
    have hn (q : Pt) : 0 ≤ (dist p q)⁻¹ := inv_nonneg.mpr dist_nonneg
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hn _)]
    rw [abs_of_nonneg (integral_nonneg hn)]
    change ∫ q in FB, (dist p q)⁻¹ ∂sphereMeasure e ≤ 4*π
    rw [← heq]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall hn)
