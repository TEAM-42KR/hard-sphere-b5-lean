import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_jacobian
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_injOn_chart
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_image_chart
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Cylinder_radial_map_volume :
    let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun y =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]
    (((volume : Measure (Fin 3 → ℝ)).restrict
      {x | 0 < x 0 ∧ -1 < x 1 ∧ x 1 < 1 ∧ 0 < x 2 ∧ x 2 < 2 * Real.pi}).withDensity
      (fun x => ENNReal.ofReal ((x 0)^2))).map f = volume := by
  let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun y =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]
  let U : Set (Fin 3 → ℝ) := {x | 0 < x 0 ∧ -1 < x 1 ∧ x 1 < 1 ∧ 0 < x 2 ∧ x 2 < 2 * Real.pi}
  have hU : MeasurableSet U := by dsimp [U]; measurability
  have hd : ∀ x ∈ U, DifferentiableAt ℝ f x := by
    intro x hx
    have hh : 1 - (x 1)^2 ≠ 0 := ne_of_gt (by nlinarith [hx.2.1, hx.2.2.1])
    apply differentiableAt_pi.2
    intro i
    fin_cases i <;> dsimp [f] <;> fun_prop (disch := assumption)
  have hdet : ∀ x ∈ U, |(fderiv ℝ f x).det| = (x 0)^2 := by
    intro x hx
    change |(fderiv ℝ f x).toLinearMap.det| = _
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)),
      SphereGeom.Aux.Cylinder.jacobian x ⟨hx.2.1, hx.2.2.1⟩,
      abs_neg, abs_of_nonneg (sq_nonneg _)]
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (Fin 3 → ℝ)) hU.nullMeasurableSet
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) SphereGeom.Aux.Cylinder.injOn_chart
  change Measure.map f ((volume.restrict U).withDensity (fun x => ENNReal.ofReal ((x 0)^2))) = _
  have hdens : (volume.restrict U).withDensity (fun x => ENNReal.ofReal ((x 0)^2)) =
      (volume.restrict U).withDensity (fun x => ENNReal.ofReal |(fderiv ℝ f x).det|) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [hdet x hx]
  rw [hdens, hm, SphereGeom.Aux.Cylinder.image_chart]
  have hn : (volume : Measure (Fin 3 → ℝ)) {y | y 1 = 0} = 0 := by
    change Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) ((Function.eval 1) ⁻¹' {0}) = 0
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  apply measure_mono_null _ hn
  intro x hx
  simp only [Set.mem_setOf_eq, not_or, not_lt] at hx
  exact not_ne_iff.mp hx.1
