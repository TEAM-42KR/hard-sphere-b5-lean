import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_inverse_sqrt_height
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option maxHeartbeats 500000

private theorem origin (q : E3) (hq : ‖q‖ ≤ 1) :
    Integrable (fun u : E3 => (dist q u)⁻¹) dOmega ∧
      (∫ u : E3, (dist q u)⁻¹ ∂dOmega) = 4 * Real.pi := by
  have hs : ∀ᵐ u ∂dOmega, ‖u‖ = 1 := by
    rw [ae_iff]
    convert SphereGeom.dOmega_compl_sphere using 1
    congr 1
    ext u
    simp [Metric.mem_sphere, dist_eq_norm]
  letI : IsFiniteMeasure dOmega := ⟨by
    change sphereMeasure 0 Set.univ < ⊤
    rw [sphereMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  by_cases hq0 : q = 0
  · subst q
    have he : (fun u : E3 => (dist 0 u)⁻¹) =ᵐ[dOmega] (fun _ => (1 : ℝ)) := by
      filter_upwards [hs] with u hu
      simp [dist_zero_left, hu]
    refine ⟨(integrable_const (1 : ℝ)).congr he.symm, ?_⟩
    rw [integral_congr_ae he, integral_const]
    simp only [measureReal_def, dOmega, sphereMeasure_univ, ENNReal.toReal_ofReal
      (by positivity : 0 ≤ 4 * Real.pi), smul_eq_mul, mul_one]
  · let r : ℝ := ‖q‖
    have hr : 0 < r := norm_pos_iff.mpr hq0
    have hr1 : r ≤ 1 := hq
    let n : E3 := r⁻¹ • q
    have hn : ‖n‖ = 1 := by
      simpa [n, r] using (norm_smul_inv_norm (𝕜 := ℝ) hq0)
    let g : ℝ → ℝ := fun t => (r * r + 1 - 2 * r * t) ^ (-1 / 2 : ℝ)
    have hg : Measurable g := by unfold g; fun_prop
    have hheight : Integrable g (volume.restrict (Set.Icc (-1) 1)) ∧
        (∫ t in Set.Icc (-1) 1, g t) = 2 := by
      have hh := HardSphereB5.SphericalCrofton.Aux.Coarea.inverse_sqrt_height r hr hr1
      constructor
      · exact (intervalIntegrable_iff_integrableOn_Icc_of_le
          (by norm_num : (-1 : ℝ) ≤ 1)).mp hh.1
      · rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact hh.2
    have hmap := SphereGeom.dOmega_map_inner n hn
    have hi : Integrable g (dOmega.map (fun u => inner ℝ n u)) := by
      rw [hmap]
      exact hheight.1.smul_measure ENNReal.ofReal_ne_top
    have hie : (fun u : E3 => (dist q u)⁻¹) =ᵐ[dOmega]
        (fun u => g (inner ℝ n u)) := by
      filter_upwards [hs] with u hu
      have hin : r * inner ℝ n u = inner ℝ q u := by
        simp only [n, real_inner_smul_left]
        rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
      have hd : dist q u ^ 2 = r * r + 1 - 2 * r * inner ℝ n u := by
        rw [dist_eq_norm, norm_sub_sq_real, hu]
        dsimp [r] at *
        nlinarith [hin]
      have ha : 0 ≤ r * r + 1 - 2 * r * inner ℝ n u := by
        rw [← hd]
        positivity
      dsimp [g]
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg ha,
        ← Real.sqrt_eq_rpow, ← hd, Real.sqrt_sq (dist_nonneg : 0 ≤ dist q u)]
    refine ⟨(hi.comp_measurable (by fun_prop)).congr hie.symm, ?_⟩
    rw [integral_congr_ae hie]
    have hm := integral_map (μ := dOmega)
      (by fun_prop : AEMeasurable (fun u : E3 => inner ℝ n u) dOmega)
      hg.stronglyMeasurable.aestronglyMeasurable
    rw [← hm, hmap, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), smul_eq_mul]
    rw [hheight.2]
    ring

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sphere_inverse_distance (c p : E3) (hp : ‖p - c‖ ≤ 1) :
    Integrable (fun v : E3 => (dist p v)⁻¹) (sphereMeasure c) ∧
      (∫ v : E3, (dist p v)⁻¹ ∂sphereMeasure c) = 4 * Real.pi := by
  have ht : dOmega.map (fun u : E3 => c + u) = sphereMeasure c := by
    unfold dOmega sphereMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, zero_add]
  have hm : MeasurableEmbedding (fun u : E3 => c + u) :=
    (Homeomorph.addLeft c).toMeasurableEquiv.measurableEmbedding
  have hd (u : E3) : dist p (c + u) = dist (p - c) u := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have ho := origin (p - c) hp
  constructor
  · rw [← ht, hm.integrable_map_iff]
    simpa only [Function.comp_def, hd] using ho.1
  · rw [← ht, hm.integral_map]
    simp_rw [hd]
    exact ho.2
