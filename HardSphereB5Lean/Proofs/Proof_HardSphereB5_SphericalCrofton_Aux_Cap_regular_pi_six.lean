import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_capInter_isRegularRegionCrofton
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_strict_cap_interior
set_option autoImplicit false

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Cap_regular_pi_six (n : Pt) (hn : ‖n‖ = 1) :
    IsRegularRegionCrofton (cap n (Real.cos (π / 6))) := by
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hc0 : 0 ≤ Real.cos (π / 6) := by rw [Real.cos_pi_div_six]; positivity
  have hc1 : Real.cos (π / 6) < 1 := by rw [Real.cos_pi_div_six]; nlinarith
  have hi : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hintn : n ∈ sInterior (cap n (Real.cos (π / 6))) := by
    simpa [SphereGeom.cap, and_self] using
      (HardSphereB5.SphericalCrofton.Aux.Geom.strict_cap_interior n n n
        (Real.cos (π / 6)) (Real.cos (π / 6)) hn (by linarith) (by linarith))
  have heq : (⋂ _ : Fin 1, cap n (Real.cos (π / 6))) = cap n (Real.cos (π / 6)) := by
    ext x
    simp only [Set.mem_iInter]
    exact ⟨fun hx => hx 0, fun hx _ => hx⟩
  have hint : (sInterior (⋂ _ : Fin 1, cap n (Real.cos (π / 6)))).Nonempty := by
    rw [heq]
    exact ⟨n, hintn⟩
  simpa only [heq] using (capInter_isRegularRegionCrofton 1 (by decide) (fun _ => n)
    (fun _ => Real.cos (π / 6)) (fun _ => hn) (fun _ => hc0) hint)
