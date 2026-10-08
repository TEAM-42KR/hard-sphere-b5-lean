import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_linearIsometryEquiv
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false

open MeasureTheory SphereGeom
open scoped ENNReal

set_option maxHeartbeats 800000

theorem proof_SphereGeom_integral_cap_moment (n : E3) (hn : ‖n‖ = 1) (h : ℝ) (h1 : -1 ≤ h) (h2 : h ≤ 1) :
    ∫ u in cap n h, u ∂dOmega = (Real.pi * (1 - h ^ 2)) • n := by
  haveI : IsFiniteMeasure dOmega := ⟨by
    change sphereMeasure 0 Set.univ < ∞
    rw [sphereMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  let p : E3 → ℝ := fun u => inner ℝ n u
  have hp : Measurable p := (continuous_const.inner continuous_id).measurable
  have hc : MeasurableSet (cap n h) := by
    change MeasurableSet ({u : E3 | ‖u‖ = 1} ∩ {u : E3 | h ≤ inner ℝ n u})
    exact (isClosed_eq continuous_norm continuous_const).measurableSet.inter
      (measurableSet_le measurable_const hp)
  have hi : Integrable (fun u : E3 => u) (dOmega.restrict (cap n h)) := by
    refine (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hc] with u hu
    exact le_of_eq hu.1
  let M : E3 := ∫ u in cap n h, u ∂dOmega
  let R : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ n).reflection
  have hRn : R n = n := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton_self n)
  have hRp (u : E3) : p (R u) = p u := by
    simpa only [hRn] using R.inner_map_map n u
  have hRc : R ⁻¹' cap n h = cap n h := by
    ext u
    change (‖R u‖ = 1 ∧ h ≤ p (R u)) ↔ (‖u‖ = 1 ∧ h ≤ p u)
    rw [R.norm_map, hRp]
  have hRμ : (dOmega.restrict (cap n h)).map R = dOmega.restrict (cap n h) := by
    calc
      (dOmega.restrict (cap n h)).map R = (dOmega.map R).restrict (cap n h) := by
        rw [Measure.restrict_map R.continuous.measurable hc, hRc]
      _ = dOmega.restrict (cap n h) := by rw [dOmega_map_linearIsometryEquiv R]
  have hRM : R M = M := by
    have hm := integral_map_of_stronglyMeasurable
      (μ := dOmega.restrict (cap n h)) R.continuous.measurable stronglyMeasurable_id
    rw [hRμ] at hm
    calc
      R M = ∫ u in cap n h, R u ∂dOmega :=
        (R.toLinearIsometry.integral_comp_comm (fun u : E3 => u)).symm
      _ = M := hm.symm
  have hM : M = (p M) • n := by
    have hf : (2 : ℝ) • ((p M) • n) - M = M := by
      simpa [R, Submodule.reflection_singleton_apply, hn, p,
        two_smul, add_smul] using hRM
    apply Eq.symm
    apply smul_right_injective E3 (by norm_num : (2 : ℝ) ≠ 0)
    simpa only [two_smul] using sub_eq_iff_eq_add.mp hf
  have hs : ∀ᵐ u ∂dOmega, ‖u‖ = 1 := by
    apply ae_iff.mpr
    simpa only [Metric.sphere, dist_zero_right, Set.compl_setOf] using dOmega_compl_sphere
  have hrestrict : dOmega.restrict (cap n h) =
      dOmega.restrict (p ⁻¹' Set.Ici h) := by
    apply Measure.restrict_congr_set
    filter_upwards [hs] with u hu
    change (‖u‖ = 1 ∧ h ≤ p u) = (h ≤ p u)
    simp only [hu, true_and]
  have hpush : (dOmega.restrict (cap n h)).map p =
      (dOmega.map p).restrict (Set.Ici h) := by
    rw [hrestrict, Measure.restrict_map hp measurableSet_Ici]
  have hsets : Set.Ici h ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc h 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨ht, _, ht1⟩
      exact ⟨ht, ht1⟩
    · rintro ⟨ht, ht1⟩
      exact ⟨ht, le_trans h1 ht, ht1⟩
  have hscalar : p M = Real.pi * (1 - h ^ 2) := by
    calc
      p M = ∫ u in cap n h, p u ∂dOmega := (integral_inner hi n).symm
      _ = ∫ t : ℝ, t ∂(dOmega.restrict (cap n h)).map p :=
        (integral_map_of_stronglyMeasurable hp stronglyMeasurable_id).symm
      _ = ∫ t : ℝ, t ∂(ENNReal.ofReal (2 * Real.pi) •
          (volume : Measure ℝ).restrict (Set.Icc h 1)) := by
        rw [hpush, dOmega_map_inner n hn, Measure.restrict_smul,
          Measure.restrict_restrict measurableSet_Ici, hsets]
      _ = (2 * Real.pi) * ((1 - h ^ 2) / 2) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2, integral_id]
        simp only [smul_eq_mul, one_pow]
      _ = Real.pi * (1 - h ^ 2) := by ring
  change M = (Real.pi * (1 - h ^ 2)) • n
  rw [hM, hscalar]
