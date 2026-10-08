import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
noncomputable section
open MeasureTheory SphereGeom

theorem proof_SphereGeom_twoBallSurface_capReduction (x y z : E3) :
  sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1) =
    dOmega (cap (y - x) (‖y - x‖ ^ 2 / 2) ∩ cap (z - x) (‖z - x‖ ^ 2 / 2)) ∧
  (∫ u in Metric.closedBall y 1 ∩ Metric.closedBall z 1, (u - x) ∂(sphereMeasure x)) =
    ∫ u in cap (y - x) (‖y - x‖ ^ 2 / 2) ∩ cap (z - x) (‖z - x‖ ^ 2 / 2), u ∂dOmega := by
  have hm : sphereMeasure x = dOmega.map (fun u : E3 => x + u) := by
    unfold dOmega sphereMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext u
    simp
  have hem : MeasurableEmbedding (fun u : E3 => x + u) :=
    (Homeomorph.addLeft x).isClosedEmbedding.measurableEmbedding
  have hs : ∀ᵐ u ∂dOmega, ‖u‖ = 1 := by
    have hc : dOmega (Metric.sphere (0 : E3) 1)ᶜ = 0 := by
      rw [dOmega, sphereMeasure, Measure.map_apply (by fun_prop) (Metric.isClosed_sphere.measurableSet.compl)]
      have hpre : (fun u : Metric.sphere (0 : E3) 1 => (0 : E3) + (u : E3)) ⁻¹'
          (Metric.sphere (0 : E3) 1)ᶜ = ∅ := by
        ext u
        simp [u.property]
      rw [hpre, measure_empty]
    have ha : ∀ᵐ u ∂dOmega, u ∈ Metric.sphere (0 : E3) 1 := mem_ae_iff.mpr hc
    filter_upwards [ha] with u hu
    simpa [Metric.mem_sphere, dist_eq_norm] using hu
  have hball (y u : E3) (hu : ‖u‖ = 1) :
      x + u ∈ Metric.closedBall y 1 ↔ u ∈ cap (y - x) (‖y - x‖ ^ 2 / 2) := by
    change x + u ∈ Metric.closedBall y 1 ↔ ‖u‖ = 1 ∧ ‖y - x‖ ^ 2 / 2 ≤ inner ℝ (y - x) u
    simp only [hu, true_and, Metric.mem_closedBall, dist_eq_norm]
    have heq : x + u - y = u - (y - x) := by abel
    rw [heq]
    have hnorm := norm_nonneg (u - (y - x))
    have hsq : ‖u - (y - x)‖ ^ 2 = 1 - 2 * inner ℝ (y - x) u + ‖y - x‖ ^ 2 := by
      rw [norm_sub_sq_real, hu, real_inner_comm]; ring
    constructor <;> intro h <;> nlinarith
  have hset : (fun u : E3 => x + u) ⁻¹' (Metric.closedBall y 1 ∩ Metric.closedBall z 1) =ᵐ[dOmega]
      ((cap (y - x) (‖y - x‖ ^ 2 / 2) ∩ cap (z - x) (‖z - x‖ ^ 2 / 2)) : Set E3) := by
    filter_upwards [hs] with u hu
    apply propext
    change (x + u ∈ Metric.closedBall y 1 ∧ x + u ∈ Metric.closedBall z 1) ↔ _
    rw [hball y u hu, hball z u hu]
    rfl
  constructor
  · rw [hm, hem.map_apply]
    exact measure_congr hset
  · rw [hm, hem.restrict_map, hem.integral_map]
    simp only [add_sub_cancel_left]
    rw [Measure.restrict_congr_set hset]
