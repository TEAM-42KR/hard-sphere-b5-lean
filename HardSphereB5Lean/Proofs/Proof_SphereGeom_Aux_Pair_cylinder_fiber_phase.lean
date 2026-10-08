import HardSphereB5Lean.Definitions.Def_SphereGeom_Aux_Pair_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom SphereGeom.Aux.Pair
noncomputable section
set_option maxHeartbeats 1000000
theorem proof_SphereGeom_Aux_Pair_cylinder_fiber_phase (z φ t : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    fiber z φ t = cylinder (Real.sqrt (1-z^2) * Real.sin t)
      (φ + (⟨-z * Real.sin t, Real.cos t⟩ : ℂ).arg) := by
  let q : ℂ := ⟨-z * Real.sin t, Real.cos t⟩
  let w : ℝ := Real.sqrt (1-z^2) * Real.sin t
  let d : ℝ := Real.sqrt (1-w^2)
  have hs : Real.sqrt (1-z^2)^2 = 1-z^2 := Real.sq_sqrt (by nlinarith [hz.1,hz.2])
  have hr : z^2 * Real.sin t^2 + Real.cos t^2 = 1-w^2 := by
    dsimp [w]
    nlinarith [Real.cos_sq_add_sin_sq t, congrArg (fun a : ℝ => a * Real.sin t^2) hs]
  have hn : ‖q‖ = d := by
    rw [Complex.norm_def]
    congr 1
    calc
      Complex.normSq q = z^2 * Real.sin t^2 + Real.cos t^2 := by simp [q,Complex.normSq]; ring
      _ = _ := hr
  have hc : d * Real.cos q.arg = -z * Real.sin t := by
    simpa only [hn,q] using Complex.norm_mul_cos_arg q
  have hsin : d * Real.sin q.arg = Real.cos t := by
    simpa only [hn,q] using Complex.norm_mul_sin_arg q
  simp only [fiber, circlePt, zero_add, one_smul, frame1, frame2, SphereGeom.Aux.Pair.cylinder]
  ext i
  fin_cases i
  · change Real.cos t * (-Real.sin φ) + Real.sin t * (-z * Real.cos φ) = d * Real.cos (φ+q.arg)
    rw [Real.cos_add]
    nlinarith [congrArg (fun a : ℝ => a * Real.cos φ) hc,
      congrArg (fun a : ℝ => a * Real.sin φ) hsin]
  · change Real.cos t * Real.cos φ + Real.sin t * (-z * Real.sin φ) = d * Real.sin (φ+q.arg)
    rw [Real.sin_add]
    nlinarith [congrArg (fun a : ℝ => a * Real.sin φ) hc,
      congrArg (fun a : ℝ => a * Real.cos φ) hsin]
  · simp [mul_comm]
