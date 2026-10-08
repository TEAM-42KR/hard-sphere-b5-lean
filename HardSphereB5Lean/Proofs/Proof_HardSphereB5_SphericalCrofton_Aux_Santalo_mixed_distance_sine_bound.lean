import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_identity
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_gram_residual_bound
set_option autoImplicit false
noncomputable section
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_sine_bound (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) (hC : IsChart D C) (t s : ℝ)
    (ht : t ∈ Set.Icc 0 C.TA) (hs : s ∈ Set.Icc 0 C.TB)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    |deriv (fun z => deriv (delta D C z) s) t| ≤
      (Real.sin (delta D C t s))⁻¹ := by
  have hmix := mixed_distance_identity D C hC t s ht hs hx
  have hnorms := HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data D hD hoff
  rcases hC with ⟨_, _, _, _, _, _, _, _, hA, hB, _, _⟩
  have hut : u D C t ∈ arcA D := by rw [hA]; exact ⟨t, ht, rfl⟩
  have hvs : v D C s ∈ arcB D := by rw [hB]; exact ⟨s, hs, rfl⟩
  have hu : ‖u D C t‖ = 1 := by
    unfold arcA at hut; split_ifs at hut <;> first | simpa using hut | exact hut.1.1
  have hv : ‖v D C s‖ = 1 := by
    unfold arcB at hvs; split_ifs at hvs <;> first | simpa using hvs | exact hvs.1.1
  let x := inner ℝ (u D C t) (v D C s)
  let L1 := inner ℝ (nAv D) (v D C s) - inner ℝ (nAv D) (u D C t) * x
  let L2 := inner ℝ (nBv D) (u D C t) - inner ℝ (nBv D) (v D C s) * x
  let S := Real.sin (Real.arccos x)
  have hS : 0 < S := by
    dsimp [S]; rw [Real.sin_arccos]; exact Real.sqrt_pos.2 (by dsimp [x]; nlinarith [hx.1, hx.2])
  have hL1 : |L1| ≤ S := by
    simpa [L1, S, Real.sin_arccos] using
      SphereGeom.Aux.Santalo.gram_residual_bound (nAv D) (u D C t) (v D C s) hnorms.1.le hu hv
  have hL2 : |L2| ≤ S := by
    have h := SphereGeom.Aux.Santalo.gram_residual_bound (nBv D) (v D C s) (u D C t) hnorms.2.1.le hv hu
    simpa [L2, S, x, real_inner_comm (v D C s) (u D C t), Real.sin_arccos] using h
  have hprod : |L1 * L2| ≤ S ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hL1 hL2 (abs_nonneg _) hS.le
  have hrewrite : |deriv (fun z => deriv (delta D C z) s) t| = |L1 * L2| / S ^ 3 := by
    have h := congrArg abs hmix
    change |-(deriv (fun z => deriv (delta D C z) s) t)| = |L1 * L2 / S ^ 3| at h
    simpa only [abs_neg, abs_div, abs_mul, abs_pow, abs_of_pos hS] using h
  rw [hrewrite]
  calc
    _ ≤ S ^ 2 / S ^ 3 := div_le_div_of_nonneg_right hprod (pow_nonneg hS.le _)
    _ = S⁻¹ := by field_simp
