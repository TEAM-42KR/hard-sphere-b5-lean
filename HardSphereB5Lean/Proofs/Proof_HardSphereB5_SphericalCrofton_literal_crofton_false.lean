import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_crofton_decomposition
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_literal_remainder_excess
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_kernel_constants
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_perim_pi_six
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_regular_pi_six
set_option autoImplicit false

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_literal_crofton_false (n : Pt) (hn : ‖n‖ = 1) (f : Kern) :
    Ff f (cap n (Real.cos (π / 6))) ≠
      cA f * sArea (cap n (Real.cos (π / 6))) - cP f * perim (cap n (Real.cos (π / 6)))
        + RfAll f (cap n (Real.cos (π / 6))) := by
  have hreg := HardSphereB5.SphericalCrofton.Aux.Cap.regular_pi_six n hn
  have hperim := HardSphereB5.SphericalCrofton.Aux.Cap.perim_pi_six n hn
  rcases kernel_constants with ⟨_, hOne, _, hCos, _⟩
  have hb : 0 < bK f := by
    cases f with
    | one =>
      rw [hOne]
      have hs0 := Real.sqrt_nonneg (3 : ℝ)
      have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      have hs : (3 / 2 : ℝ) < Real.sqrt 3 := by nlinarith
      have hpi22 : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
      linarith
    | cos =>
      rw [hCos]
      positivity
  rw [crofton_decomposition hreg f, literal_remainder_excess hreg f, hperim]
  have hp := mul_pos hb Real.pi_pos
  intro heq
  have hcut : 2 * π - π = π := by ring
  rw [hcut] at heq
  linarith
