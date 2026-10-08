import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_dOmega_cap (n : E3) (hn : ‖n‖ = 1) (h : ℝ) (h1 : -1 ≤ h) (h2 : h ≤ 1) :
    dOmega (cap n h) = ENNReal.ofReal (2 * Real.pi * (1 - h)) := by
  have hf : Measurable (fun u : E3 => inner ℝ n u) := measurable_const.inner measurable_id
  have hs : cap n h = (fun u : E3 => inner ℝ n u) ⁻¹' Set.Ici h ∩ Metric.sphere (0 : E3) 1 := by
    ext u
    simp [cap, Metric.mem_sphere, dist_zero_right, and_comm]
  rw [hs, measure_inter_conull SphereGeom.dOmega_compl_sphere]
  rw [← Measure.map_apply hf measurableSet_Ici,
      SphereGeom.dOmega_map_inner n hn, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply measurableSet_Ici]
  have hi : Set.Ici h ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc h 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨a, b, c⟩
      exact ⟨a, c⟩
    · rintro ⟨a, b⟩
      exact ⟨a, le_trans h1 a, b⟩
  rw [hi, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
