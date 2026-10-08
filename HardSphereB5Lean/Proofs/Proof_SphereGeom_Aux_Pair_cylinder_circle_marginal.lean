import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_angle_average
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_cylinder_sineHeightMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
set_option maxHeartbeats 1500000
theorem proof_SphereGeom_Aux_Pair_cylinder_circle_marginal (f : E3 → ENNReal) (hf : Measurable f) :
    (∫⁻ z in Set.Icc (-1 : ℝ) 1, ∫⁻ φ in Set.Ico 0 (2 * Real.pi),
      ∫⁻ t in Set.Ico 0 (2 * Real.pi),
        f (circlePt 0 (WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0])
          (WithLp.toLp 2 ![-z * Real.cos φ, -z * Real.sin φ, Real.sqrt (1-z^2)]) 1 t)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, f u ∂dOmega := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Set.Ico 0 (2 * Real.pi))
  let C : ℝ → ℝ → E3 := fun z φ => WithLp.toLp 2
    ![Real.sqrt (1-z^2) * Real.cos φ, Real.sqrt (1-z^2) * Real.sin φ, z]
  let U : ℝ → ℝ → ℝ → E3 := fun z φ t => WithLp.toLp 2
    ![-Real.cos t * Real.sin φ - z * Real.sin t * Real.cos φ,
      Real.cos t * Real.cos φ - z * Real.sin t * Real.sin φ,
      Real.sqrt (1-z^2) * Real.sin t]
  let k : ℝ → ENNReal := fun w => ∫⁻ φ, f (C w φ) ∂ν
  let w : ℝ × ℝ → ℝ := fun x => Real.sqrt (1-x.1^2) * Real.sin x.2
  have hC : Measurable (Function.uncurry C) := by dsimp [C, Function.uncurry]; fun_prop
  have hk : Measurable k := Measurable.lintegral_prod_right
    (f := fun w φ => f (C w φ)) (hf.comp hC)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hpoint (z φ t : ℝ) : circlePt 0 (WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0])
        (WithLp.toLp 2 ![-z * Real.cos φ, -z * Real.sin φ, Real.sqrt (1-z^2)]) 1 t = U z φ t := by
    ext i
    fin_cases i <;> simp [circlePt, U] <;> ring
  have he : Orthonormal ℝ (![WithLp.toLp 2 ![1,0,0], WithLp.toLp 2 ![0,1,0],
      WithLp.toLp 2 ![0,0,1]] : Fin 3 → E3) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]
  have hmap : (μ.prod ν).map (Function.uncurry C) = dOmega := by
    have h := dOmega_map_cylinder _ he
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    convert h.symm using 1
    congr 1
    funext x
    ext i
    fin_cases i <;> simp [C, Function.uncurry]
  have htotal : (∫⁻ u, f u ∂dOmega) = ∫⁻ z, k z ∂μ := by
    rw [← hmap, lintegral_map hf hC]
    exact lintegral_prod _ (hf.comp hC).aemeasurable
  simp_rw [hpoint]
  change (∫⁻ z, ∫⁻ φ, ∫⁻ t, f (U z φ t) ∂ν ∂ν ∂μ) =
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, f u ∂dOmega
  calc
    (∫⁻ z, ∫⁻ φ, ∫⁻ t, f (U z φ t) ∂ν ∂ν ∂μ) =
        ∫⁻ z, ∫⁻ t, ∫⁻ φ, f (U z φ t) ∂ν ∂ν ∂μ := by
      apply lintegral_congr
      intro z
      apply lintegral_lintegral_swap
      exact (hf.comp (show Measurable (fun x : ℝ × ℝ => U z x.1 x.2) by
        dsimp [U]; fun_prop)).aemeasurable
    _ = ∫⁻ z, ∫⁻ t, k (w (z,t)) ∂ν ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      apply lintegral_congr
      intro t
      have hs : Real.sqrt (1-z^2)^2 = 1-z^2 := Real.sq_sqrt (by nlinarith [hz.1, hz.2])
      have hr : z^2 * Real.sin t^2 + Real.cos t^2 = 1 - (Real.sqrt (1-z^2)*Real.sin t)^2 := by
        nlinarith [Real.cos_sq_add_sin_sq t,
          congrArg (fun a : ℝ => a * Real.sin t^2) hs]
      simpa [U, k, C, w, hr, ν] using SphereGeom.Aux.Pair.cylinder_angle_average f z t
    _ = ∫⁻ x, k (w x) ∂μ.prod ν := (lintegral_prod _ (hk.comp hw).aemeasurable).symm
    _ = ∫⁻ h, k h ∂(μ.prod ν).map w := (lintegral_map hk hw).symm
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ z, k z ∂μ := by
      rw [show (μ.prod ν).map w = ENNReal.ofReal (2 * Real.pi) • μ from
        SphereGeom.Aux.Pair.cylinder_sineHeightMeasure, lintegral_smul_measure]
      rfl
    _ = _ := by rw [htotal]
