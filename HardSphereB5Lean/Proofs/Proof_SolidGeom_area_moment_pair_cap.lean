import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_cap
import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_cap_moment
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
set_option autoImplicit false

noncomputable section
open MeasureTheory Real SphereGeom

theorem proof_SolidGeom_area_moment_pair_cap (x y : E3) (h0 : 0 < dist x y) (h2 : dist x y < 2) :
    (sphereMeasure x (Metric.closedBall y 1)).toReal = 2 * π * (1 - dist x y / 2) ∧
      ∫ u in Metric.closedBall y 1, (u - x) ∂(sphereMeasure x) =
        (π * (1 - dist x y ^ 2 / 4) / dist x y) • (y - x) := by
  let d := dist x y
  let v := y - x
  let n := d⁻¹ • v
  have hd : 0 < d := h0
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hv : ‖v‖ = d := by simp [v, d, dist_eq_norm, norm_sub_rev]
  have hn : ‖n‖ = 1 := by
    simp [n, norm_smul, Real.norm_eq_abs, abs_of_pos hd, hv, hd0]
  have hh0 : -1 ≤ d / 2 := by linarith
  have hh1 : d / 2 ≤ 1 := by dsimp [d]; linarith
  have hm : sphereMeasure x = dOmega.map (fun u : E3 => x + u) := by
    unfold dOmega sphereMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext u
    simp
  have hem : MeasurableEmbedding (fun u : E3 => x + u) :=
    (Homeomorph.addLeft x).isClosedEmbedding.measurableEmbedding
  have hs : ∀ᵐ u ∂dOmega, ‖u‖ = 1 := by
    have h := SphereGeom.dOmega_compl_sphere
    have ha : ∀ᵐ u ∂dOmega, u ∈ Metric.sphere (0 : E3) 1 := by
      exact mem_ae_iff.mpr h
    filter_upwards [ha] with u hu
    simpa [Metric.mem_sphere, dist_eq_norm] using hu
  have hset : (fun u : E3 => x + u) ⁻¹' Metric.closedBall y 1 =ᵐ[dOmega] cap n (d / 2) := by
    filter_upwards [hs] with u hu
    apply propext
    change (x + u ∈ Metric.closedBall y 1) ↔ (‖u‖ = 1 ∧ d / 2 ≤ inner ℝ n u)
    simp only [hu, true_and, Metric.mem_closedBall, dist_eq_norm]
    have heq : x + u - y = u - v := by dsimp [v]; abel
    rw [heq]
    have hi : inner ℝ n u = d⁻¹ * inner ℝ u v := by
      dsimp [n]
      rw [real_inner_smul_left, real_inner_comm]
    have hnorm := norm_nonneg (u - v)
    have hsq : ‖u - v‖ ^ 2 = 1 - 2 * inner ℝ u v + d ^ 2 := by
      rw [norm_sub_sq_real, hu, hv]; ring
    rw [hi]
    constructor
    · intro h
      have hb : ‖u - v‖ ^ 2 ≤ 1 := by nlinarith
      have hj : d ^ 2 / 2 ≤ inner ℝ u v := by nlinarith
      apply (le_inv_mul_iff₀ hd).2
      nlinarith
    · intro h
      have hj := (le_inv_mul_iff₀ hd).1 h
      nlinarith
  have harea : sphereMeasure x (Metric.closedBall y 1) = dOmega (cap n (d / 2)) := by
    rw [hm, hem.map_apply]
    exact measure_congr hset
  have hint : (∫ u in Metric.closedBall y 1, (u - x) ∂(sphereMeasure x)) =
      ∫ u in cap n (d / 2), u ∂dOmega := by
    rw [hm, hem.restrict_map, hem.integral_map]
    have hre := Measure.restrict_congr_set hset
    simp only [add_sub_cancel_left]
    rw [hre]
  constructor
  · have hp : 0 ≤ 2 * π * (1 - d / 2) := by positivity
    rw [harea, SphereGeom.dOmega_cap n hn (d / 2) hh0 hh1, ENNReal.toReal_ofReal hp]
  · rw [hint, SphereGeom.integral_cap_moment n hn (d / 2) hh0 hh1]
    dsimp [n, v]
    rw [smul_smul]
    congr 1
    dsimp [d]
    ring
