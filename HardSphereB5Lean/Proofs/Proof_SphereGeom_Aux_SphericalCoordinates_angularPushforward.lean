import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SphericalCoordinates_cosHeightMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
set_option autoImplicit false

open MeasureTheory SphereGeom
open scoped ENNReal

noncomputable section

theorem proof_SphereGeom_Aux_SphericalCoordinates_angularPushforward :
    let coord : ℝ × ℝ → E3 := fun p =>
      (Real.sin p.1 * Real.cos p.2) • (EuclideanSpace.basisFun (Fin 3) ℝ) 0 +
      (Real.sin p.1 * Real.sin p.2) • (EuclideanSpace.basisFun (Fin 3) ℝ) 1 +
      Real.cos p.1 • (EuclideanSpace.basisFun (Fin 3) ℝ) 2
    (((volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi)).prod
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))).withDensity
      (fun p => ENNReal.ofReal (Real.sin p.1)) |>.map coord = dOmega := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let μθ : Measure ℝ := volume.restrict (Set.Ioc 0 Real.pi)
  let μφ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let w : ℝ → ℝ≥0∞ := fun θ => ENNReal.ofReal (Real.sin θ)
  let μ : Measure (ℝ × ℝ) := (μθ.prod μφ).withDensity (fun p => w p.1)
  let T : ℝ × ℝ → ℝ × ℝ := Prod.map Real.cos id
  let C : ℝ × ℝ → E3 := fun x =>
    (Real.sqrt (1 - x.1 ^ 2) * Real.cos x.2) • b 0 +
    (Real.sqrt (1 - x.1 ^ 2) * Real.sin x.2) • b 1 + x.1 • b 2
  have hw : Measurable w := by unfold w; fun_prop
  have hT : Measurable T := Real.measurable_cos.prodMap measurable_id
  have hC : Measurable C := by unfold C; fun_prop
  have hdensity : (μθ.withDensity w).prod μφ = μ := prod_withDensity_left hw
  have hTmap : μ.map T =
      (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico 0 (2 * Real.pi)) := by
    rw [← hdensity, ← Measure.map_prod_map _ _ Real.measurable_cos measurable_id]
    rw [show (μθ.withDensity w).map Real.cos = volume.restrict (Set.Icc (-1 : ℝ) 1) from
      SphereGeom.Aux.SphericalCoordinates.cosHeightMeasure]
    simp only [Measure.map_id]
    rw [show μφ = volume.restrict (Set.Ico (0 : ℝ) (2 * Real.pi)) from
      restrict_Ico_eq_restrict_Ioc.symm]
    exact Measure.prod_restrict _ _
  have hae : ∀ᵐ p ∂μ, p.1 ∈ Set.Ioc (0 : ℝ) Real.pi := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    change ∀ᵐ p ∂(volume.restrict (Set.Ioc (0 : ℝ) Real.pi)).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))), p.1 ∈ Set.Ioc (0 : ℝ) Real.pi
    rw [Measure.prod_restrict]
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    exact hp.1
  change μ.map _ = dOmega
  calc
    μ.map _ = μ.map (C ∘ T) := by
      apply Measure.map_congr
      filter_upwards [hae] with p hp
      have hsin : 0 ≤ Real.sin p.1 := Real.sin_nonneg_of_nonneg_of_le_pi hp.1.le hp.2
      have hsqrt : Real.sqrt (1 - Real.cos p.1 ^ 2) = Real.sin p.1 := by
        rw [← Real.sin_sq_add_cos_sq p.1]
        ring_nf
        exact Real.sqrt_sq hsin
      simp [Function.comp_apply, C, T, Prod.map_apply, id_eq, hsqrt, b]
    _ = (μ.map T).map C := (Measure.map_map hC hT).symm
    _ = dOmega := by
      rw [hTmap]
      exact (SphereGeom.dOmega_map_cylinder b b.orthonormal).symm
