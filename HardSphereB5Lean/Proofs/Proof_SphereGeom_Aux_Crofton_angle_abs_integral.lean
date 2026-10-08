import Mathlib
set_option autoImplicit false

open MeasureTheory

theorem proof_SphereGeom_Aux_Crofton_angle_abs_integral (A B : ℝ) :
    (∫ ψ in (0 : ℝ)..(2 * Real.pi), |A * Real.cos ψ + B * Real.sin ψ|) =
      4 * Real.sqrt (A ^ 2 + B ^ 2) := by
  have hc : Continuous (fun x : ℝ => |Real.sin x|) := Real.continuous_sin.abs
  have hp : Function.Periodic (fun x : ℝ => |Real.sin x|) Real.pi := by
    intro x
    simp [Real.sin_add_pi]
  have hhalf : (∫ x in (0 : ℝ)..Real.pi, |Real.sin x|) = 2 := by
    calc
      _ = ∫ x in (0 : ℝ)..Real.pi, Real.sin x := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply abs_of_nonneg
        apply Real.sin_nonneg_of_mem_Icc
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hx
      _ = 2 := by rw [integral_sin]; norm_num
  have hother : (∫ x in Real.pi..(2 * Real.pi), |Real.sin x|) = 2 := by
    have ht := hp.intervalIntegral_add_eq Real.pi 0
    simpa only [zero_add, ← two_mul, hhalf] using ht
  have hfull : (∫ x in (0 : ℝ)..(2 * Real.pi), |Real.sin x|) = 4 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 Real.pi) (hc.intervalIntegrable Real.pi (2 * Real.pi)),
      hhalf, hother]
    norm_num
  have hp2 : Function.Periodic (fun x : ℝ => |Real.sin x|) (2 * Real.pi) := by
    intro x
    simp [Real.sin_add_two_pi]
  let z : ℂ := ⟨B, A⟩
  have hzA : ‖z‖ * Real.sin z.arg = A := Complex.norm_mul_sin_arg z
  have hzB : ‖z‖ * Real.cos z.arg = B := Complex.norm_mul_cos_arg z
  have hrepr (x : ℝ) :
      A * Real.cos x + B * Real.sin x = ‖z‖ * Real.sin (x + z.arg) := by
    rw [Real.sin_add]
    calc
      _ = (‖z‖ * Real.sin z.arg) * Real.cos x +
          (‖z‖ * Real.cos z.arg) * Real.sin x := by rw [hzA, hzB]
      _ = _ := by ring
  have hnorm : ‖z‖ = Real.sqrt (A ^ 2 + B ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    dsimp [z]
    congr 1
    ring
  calc
    _ = ∫ x in (0 : ℝ)..(2 * Real.pi), ‖z‖ * |Real.sin (x + z.arg)| := by
      apply intervalIntegral.integral_congr
      intro x hx
      change |A * Real.cos x + B * Real.sin x| = ‖z‖ * |Real.sin (x + z.arg)|
      rw [hrepr, abs_mul, abs_of_nonneg (norm_nonneg z)]
    _ = ‖z‖ * (∫ x in (0 : ℝ)..(2 * Real.pi), |Real.sin (x + z.arg)|) :=
      intervalIntegral.integral_const_mul _ _
    _ = ‖z‖ * (∫ x in z.arg..(z.arg + 2 * Real.pi), |Real.sin x|) := by
      congr 1
      simpa only [zero_add, add_comm (2 * Real.pi)] using
        (intervalIntegral.integral_comp_add_right (f := fun x : ℝ => |Real.sin x|)
          (a := 0) (b := 2 * Real.pi) z.arg)
    _ = ‖z‖ * 4 := by
      rw [hp2.intervalIntegral_add_eq z.arg 0, zero_add, hfull]
    _ = 4 * Real.sqrt (A ^ 2 + B ^ 2) := by rw [hnorm]; ring
