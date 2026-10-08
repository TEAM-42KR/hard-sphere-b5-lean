import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false
open MeasureTheory Real SphereGeom Set Metric

theorem proof_SolidGeom_sphereMeasure_sphere_inter_null (c d : E3) (hcd : c ≠ d) :
    sphereMeasure c (Metric.sphere d 1) = 0 := by
  let v : E3 := d - c
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd)
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let n : E3 := ‖v‖⁻¹ • v
  have hn : ‖n‖ = 1 := by
    simp [n, norm_smul, abs_of_nonneg (norm_nonneg v), hnv]
  have hlev : dOmega {u : E3 | inner ℝ n u = ‖v‖ / 2} = 0 := by
    have hmeas : Measurable (fun u : E3 => inner ℝ n u) := by fun_prop
    have hpre : (fun u : E3 => inner ℝ n u) ⁻¹' {‖v‖ / 2} =
        {u : E3 | inner ℝ n u = ‖v‖ / 2} := rfl
    rw [← hpre, ← Measure.map_apply hmeas (measurableSet_singleton _),
      SphereGeom.dOmega_map_inner n hn, Measure.smul_apply]
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    have hz : (volume : Measure ℝ) ({‖v‖ / 2} ∩ Icc (-1) 1) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton _)
    rw [hz, smul_zero]
  have hcalc (u : sphere (0 : E3) 1) (hu : c + (u : E3) ∈ sphere d 1) :
      inner ℝ n (u : E3) = ‖v‖ / 2 := by
    have hu1 : ‖(u : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using u.property
    have hu2 : ‖(u : E3) - v‖ = 1 := by
      have ht : c + (u : E3) - d = (u : E3) - v := by dsimp [v]; abel
      simpa only [Metric.mem_sphere, dist_eq_norm, ht] using hu
    have hp : inner ℝ (u : E3) v = ‖v‖ ^ 2 / 2 := by
      have h := norm_sub_sq_real (u : E3) v
      rw [hu1, hu2] at h
      nlinarith
    dsimp [n]
    rw [real_inner_smul_left, real_inner_comm (u : E3) v, hp]
    field_simp
  rw [sphereMeasure, Measure.map_apply (by fun_prop) isClosed_sphere.measurableSet]
  apply le_antisymm _ (zero_le)
  calc
    (volume : Measure E3).toSphere ((fun u : sphere (0 : E3) 1 => c + (u : E3)) ⁻¹' sphere d 1) ≤
      (volume : Measure E3).toSphere {u : sphere (0 : E3) 1 | inner ℝ n (u : E3) = ‖v‖ / 2} :=
      measure_mono (fun u hu => hcalc u hu)
    _ = dOmega {u : E3 | inner ℝ n u = ‖v‖ / 2} := by
      rw [dOmega, sphereMeasure, Measure.map_apply (by fun_prop) (by measurability)]
      simp
    _ = 0 := hlev
