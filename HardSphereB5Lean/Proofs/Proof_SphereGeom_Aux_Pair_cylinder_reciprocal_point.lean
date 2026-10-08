import HardSphereB5Lean.Definitions.Def_SphereGeom_Aux_Pair_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom SphereGeom.Aux.Pair
noncomputable section
set_option maxHeartbeats 1000000
theorem proof_SphereGeom_Aux_Pair_cylinder_reciprocal_point (z t ψ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hw : (Real.sqrt (1-z^2) * Real.sin t)^2 < 1) :
    cylinder z (ψ - (⟨-z * Real.sin t, Real.cos t⟩ : ℂ).arg) =
      reciprocal (meridian z t) ψ := by
  let r : ℝ := Real.sqrt (1-z^2)
  let w : ℝ := r * Real.sin t
  let d : ℝ := Real.sqrt (1-w^2)
  let q : ℂ := ⟨-z * Real.sin t, Real.cos t⟩
  have hr : r^2 = 1-z^2 := Real.sq_sqrt (by nlinarith [hz.1,hz.2])
  have hd : 0 < d := Real.sqrt_pos.mpr (by dsimp [w,r]; linarith)
  have heq : z^2 * Real.sin t^2 + Real.cos t^2 = 1-w^2 := by
    dsimp [w]
    nlinarith [Real.cos_sq_add_sin_sq t, congrArg (fun a : ℝ => a * Real.sin t^2) hr]
  have hnorm : ‖q‖ = d := by
    rw [Complex.norm_def]
    change Real.sqrt (Complex.normSq q) = Real.sqrt (1-w^2)
    congr 1
    calc
      Complex.normSq q = z^2 * Real.sin t^2 + Real.cos t^2 := by simp [q, Complex.normSq]; ring
      _ = _ := heq
  have hc : d * Real.cos q.arg = -z * Real.sin t := by
    simpa only [hnorm,q] using Complex.norm_mul_cos_arg q
  have hs : d * Real.sin q.arg = Real.cos t := by
    simpa only [hnorm,q] using Complex.norm_mul_sin_arg q
  ext i
  fin_cases i
  · change r * Real.cos (ψ-q.arg) = (-r * Real.cos t / d) * (-Real.sin ψ) +
      (z / d) * (-w * Real.cos ψ)
    rw [Real.cos_sub]
    field_simp [hd.ne']
    dsimp [w]
    nlinarith [congrArg (fun a : ℝ => r * Real.cos ψ * a) hc,
      congrArg (fun a : ℝ => r * Real.sin ψ * a) hs]
  · change r * Real.sin (ψ-q.arg) = (-r * Real.cos t / d) * Real.cos ψ +
      (z / d) * (-w * Real.sin ψ)
    rw [Real.sin_sub]
    field_simp [hd.ne']
    dsimp [w]
    nlinarith [congrArg (fun a : ℝ => r * Real.sin ψ * a) hc,
      congrArg (fun a : ℝ => r * Real.cos ψ * a) hs]
  · change z = (-r * Real.cos t / d) * 0 + (z / d) * d
    field_simp [hd.ne']
    ring
