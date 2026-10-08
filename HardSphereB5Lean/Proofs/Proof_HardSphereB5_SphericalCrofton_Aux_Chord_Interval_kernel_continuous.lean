import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_kernel_continuous (f : Kern) : Continuous (kK f) := by
  let q : ℝ → ℝ := fun t => wK f (Real.cos t) * Real.sin t
  have hq : Continuous q := by
    cases f
    · simpa [q, wK] using Real.continuous_sin
    · change Continuous (fun t : ℝ => Real.cos t * Real.sin t)
      exact Real.continuous_cos.mul Real.continuous_sin
  have hA : Continuous (fun L : ℝ => ∫ t in (0 : ℝ)..L, q t) :=
    intervalIntegral.continuous_primitive (fun _ _ => hq.intervalIntegrable _ _) 0
  have hB : Continuous (fun L : ℝ => ∫ t in (0 : ℝ)..L, t * q t) :=
    intervalIntegral.continuous_primitive
      (fun _ _ => (continuous_id.mul hq).intervalIntegrable _ _) 0
  have hmin : Continuous (fun L : ℝ => min L (π / 3)) := continuous_id.min continuous_const
  have he (L : ℝ) : kK f L =
      2 * (L * (∫ t in (0 : ℝ)..(min L (π / 3)), q t) -
        (∫ t in (0 : ℝ)..(min L (π / 3)), t * q t)) := by
    unfold kK
    have hp : (fun t => (L - t) * wK f (Real.cos t) * Real.sin t) =
        (fun t => L * q t - t * q t) := by
      funext t
      dsimp [q]
      ring
    have ha : IntervalIntegrable (fun t : ℝ => L * q t) volume 0 (min L (π / 3)) :=
      ((continuous_const : Continuous (fun _ : ℝ => L)).mul hq).intervalIntegrable _ _
    have hb : IntervalIntegrable (fun t : ℝ => t * q t) volume 0 (min L (π / 3)) :=
      (continuous_id.mul hq).intervalIntegrable _ _
    rw [hp, intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul]
  change Continuous (fun L : ℝ => kK f L)
  simp_rw [he]
  exact continuous_const.mul ((continuous_id.mul (hA.comp hmin)).sub (hB.comp hmin))
