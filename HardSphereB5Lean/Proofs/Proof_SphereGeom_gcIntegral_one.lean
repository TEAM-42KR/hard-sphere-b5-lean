import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_gcIntegral_one : gcIntegral (fun _ => 1) = 2 * Real.pi := by
  have hmass (c : E3) : sphereMeasure c Set.univ = ENNReal.ofReal (4 * Real.pi) := by
    have hm : Measurable (fun u : Metric.sphere (0 : E3) 1 => c + (u : E3)) :=
      measurable_const.add measurable_subtype_coe
    rw [sphereMeasure, Measure.map_apply hm MeasurableSet.univ]
    simp only [Set.preimage_univ, Measure.toSphere_apply_univ]
    have hd : Module.finrank ℝ E3 = 2 * 1 + 1 := by simp [E3]
    rw [InnerProductSpace.volume_ball_of_dim_odd hd]
    norm_num [E3, Nat.doubleFactorial]
    rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num,
      show (4 : ENNReal) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  unfold gcIntegral
  rw [integral_const]
  simp only [smul_eq_mul, mul_one, measureReal_def, dOmega, hmass]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring
