import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Archimedes_cone_volume_Iic
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Pointwise

theorem proof_SphereGeom_dOmega_map_inner (n : E3) (hn : ‖n‖ = 1) :
    dOmega.map (fun u => inner ℝ n u) =
      ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1) := by
  letI : IsFiniteMeasure dOmega := by unfold dOmega sphereMeasure; infer_instance
  apply Measure.ext_of_Iic
  intro h
  have hf : Measurable (fun u : E3 => inner ℝ n u) := measurable_const.inner measurable_id
  have hg : Measurable (fun u : Metric.sphere (0 : E3) 1 => (0 : E3) + (u : E3)) := by fun_prop
  rw [Measure.map_apply hf measurableSet_Iic]
  unfold dOmega sphereMeasure
  rw [Measure.map_apply hg (hf measurableSet_Iic)]
  have hs : MeasurableSet {u : Metric.sphere (0 : E3) 1 | inner ℝ n (u : E3) ≤ h} := by
    exact measurableSet_le (measurable_const.inner measurable_subtype_coe) measurable_const
  simp only [zero_add]
  change volume.toSphere {u : Metric.sphere (0 : E3) 1 | inner ℝ n (u : E3) ≤ h} = _
  rw [Measure.toSphere_apply' _ hs]
  rw [SphereGeom.Aux.Archimedes.cone_volume_Iic n hn h]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Iic]
  have hi : Set.Iic h ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) (min h 1) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    tauto
  rw [hi, Real.volume_Icc]
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
