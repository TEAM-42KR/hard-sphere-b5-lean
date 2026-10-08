import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_periodic_lintegral_translate
set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
set_option maxHeartbeats 800000
theorem proof_SphereGeom_Aux_Pair_cylinder_angle_average (f : E3 → ENNReal) (z t : ℝ) :
    (∫⁻ φ in Set.Ico 0 (2 * Real.pi), f (WithLp.toLp 2
      ![-Real.cos t * Real.sin φ - z * Real.sin t * Real.cos φ,
        Real.cos t * Real.cos φ - z * Real.sin t * Real.sin φ,
        Real.sqrt (1-z^2) * Real.sin t] : E3)) =
    (∫⁻ φ in Set.Ico 0 (2 * Real.pi), f (WithLp.toLp 2
      ![Real.sqrt (z^2 * Real.sin t^2 + Real.cos t^2) * Real.cos φ,
        Real.sqrt (z^2 * Real.sin t^2 + Real.cos t^2) * Real.sin φ,
        Real.sqrt (1-z^2) * Real.sin t] : E3)) := by
  let q : ℂ := ⟨-z * Real.sin t, Real.cos t⟩
  let r : ℝ := Real.sqrt (z^2 * Real.sin t^2 + Real.cos t^2)
  have hn : ‖q‖ = r := by
    rw [Complex.norm_def]
    congr 1
    simp [q, Complex.normSq]
    ring
  have hcos : r * Real.cos q.arg = -z * Real.sin t := by
    simpa only [hn, q] using Complex.norm_mul_cos_arg q
  have hsin : r * Real.sin q.arg = Real.cos t := by
    simpa only [hn, q] using Complex.norm_mul_sin_arg q
  let g : ℝ → ENNReal := fun φ => f (WithLp.toLp 2 ![r * Real.cos φ, r * Real.sin φ,
    Real.sqrt (1-z^2) * Real.sin t])
  have hg : Function.Periodic g (2 * Real.pi) := by
    intro φ
    simp [g, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hpoint (φ : ℝ) : (WithLp.toLp 2
      ![-Real.cos t * Real.sin φ - z * Real.sin t * Real.cos φ,
        Real.cos t * Real.cos φ - z * Real.sin t * Real.sin φ,
        Real.sqrt (1-z^2) * Real.sin t] : E3) =
      WithLp.toLp 2 ![r * Real.cos (φ + q.arg), r * Real.sin (φ + q.arg),
        Real.sqrt (1-z^2) * Real.sin t] := by
    ext i
    fin_cases i
    · change -Real.cos t * Real.sin φ - z * Real.sin t * Real.cos φ = r * Real.cos (φ + q.arg)
      rw [Real.cos_add]
      nlinarith [congrArg (fun a : ℝ => a * Real.cos φ) hcos,
        congrArg (fun a : ℝ => a * Real.sin φ) hsin]
    · change Real.cos t * Real.cos φ - z * Real.sin t * Real.sin φ = r * Real.sin (φ + q.arg)
      rw [Real.sin_add]
      nlinarith [congrArg (fun a : ℝ => a * Real.sin φ) hcos,
        congrArg (fun a : ℝ => a * Real.cos φ) hsin]
    · rfl
  simp_rw [hpoint]
  change (∫⁻ φ in Set.Ico 0 (2 * Real.pi), g (φ + q.arg)) =
    ∫⁻ φ in Set.Ico 0 (2 * Real.pi), g φ
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa only [zero_add] using SphereGeom.Aux.Pair.periodic_lintegral_translate g (2 * Real.pi)
    (by positivity) hg 0 q.arg
