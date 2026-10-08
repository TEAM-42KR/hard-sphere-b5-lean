import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_sphere_slice_circle_image
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom
open scoped Classical
set_option maxHeartbeats 900000

theorem proof_SphereGeom_Aux_activeSphereCircle_measure_le (v : E3) (hv0 : v ≠ 0) (hv1 : ‖v‖ ≤ 1) :
    arcMeasure {u : E3 | ‖u‖ = 1 ∧ ‖v + u‖ = 1} ≤ ENNReal.ofReal (2 * Real.pi) := by
  have hane : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  let m : E3 := ‖v‖⁻¹ • (-v)
  have hm : ‖m‖ = 1 := by
    simp [m, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v), hane]
  obtain ⟨F₁,F₂,hF₁,hF₂,hF⟩ := SphereGeom.exists_measurable_frame
  let E : Fin 3 → E3 := ![F₁ m,F₂ m,m]
  have hE : Orthonormal ℝ E := hF m hm
  let r : ℝ := Real.sqrt (1 - (‖v‖ / 2) ^ 2)
  have hz : |‖v‖ / 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hr : 0 < r := Real.sqrt_pos.mpr (by
    have hnn := norm_nonneg v
    nlinarith)
  have hr1 : r ≤ 1 := by
    have hs : r ^ 2 = 1 - (‖v‖ / 2) ^ 2 := Real.sq_sqrt (by
      have hnn := norm_nonneg v
      nlinarith)
    nlinarith [Real.sqrt_nonneg (1 - (‖v‖ / 2) ^ 2), sq_nonneg (‖v‖ / 2)]
  let c : E3 := (‖v‖ / 2) • E 2
  let γ : ℝ → E3 := circlePt c (E 0) (E 1) r
  have hsub : {u : E3 | ‖u‖ = 1 ∧ ‖v + u‖ = 1} ⊆ γ '' Set.Icc (0 : ℝ) (2 * π) := by
    intro u hu
    have hi : inner ℝ v u = -‖v‖ ^ 2 / 2 := by
      have hs := norm_add_sq_real v u
      rw [hu.2,hu.1] at hs
      nlinarith
    have hmi : inner ℝ (E 2) u = ‖v‖ / 2 := by
      change inner ℝ m u = ‖v‖ / 2
      dsimp [m]
      rw [real_inner_smul_left, inner_neg_left, hi]
      field_simp
    have hu' : u ∈ {u : E3 | ‖u‖ = 1 ∧ inner ℝ (E 2) u = ‖v‖ / 2} := ⟨hu.1,hmi⟩
    rw [SphereGeom.Aux.sphere_slice_circle_image E hE (‖v‖ / 2) hz] at hu'
    exact hu'
  have hE2 : Orthonormal ℝ ![E 0,E 1] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (1 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (1 : Fin 3)
  have hγ : Measurable γ := by dsimp [γ]; unfold circlePt; fun_prop
  have hmass : arcMeasure (γ '' Set.Icc (0 : ℝ) (2 * π)) =
      ENNReal.ofReal r * ENNReal.ofReal (2 * π) := by
    have hh := congrArg (fun μ : Measure E3 => μ Set.univ)
      (SphereGeom.arcMeasure_restrict_circle c ![E 0,E 1] hE2 r hr 0 (2 * π)
        (by positivity) (by linarith))
    change (arcMeasure.restrict (γ '' Set.Icc (0 : ℝ) (2 * π))) Set.univ =
      (ENNReal.ofReal r • ((volume.restrict (Set.Icc (0 : ℝ) (2 * π))).map γ)) Set.univ at hh
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.smul_apply,
      Measure.map_apply hγ MeasurableSet.univ] at hh
    simpa [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Real.volume_Icc] using hh
  calc
    arcMeasure {u : E3 | ‖u‖ = 1 ∧ ‖v + u‖ = 1}
        ≤ arcMeasure (γ '' Set.Icc (0 : ℝ) (2 * π)) := measure_mono hsub
    _ = ENNReal.ofReal r * ENNReal.ofReal (2 * π) := hmass
    _ ≤ 1 * ENNReal.ofReal (2 * π) := by
      gcongr
      simpa using ENNReal.ofReal_le_ofReal hr1
    _ = ENNReal.ofReal (2 * π) := one_mul _
