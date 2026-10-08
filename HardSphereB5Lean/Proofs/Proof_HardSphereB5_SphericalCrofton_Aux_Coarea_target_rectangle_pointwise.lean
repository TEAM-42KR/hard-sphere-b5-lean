import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_center_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_centerFrame_nonzero
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_axis_exclusion
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_incidence_regular
set_option autoImplicit false

open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section
set_option maxHeartbeats 1000000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_rectangle_pointwise (y : Chart5)
    (h0 : y 0 ∈ Set.Ioo (1/2 : ℝ) 1) (h2 : y 2 ∈ Set.Ioo (-1 : ℝ) (-1/2))
    (h1 : y 1 ∈ Set.Ioo (-Real.pi) Real.pi)
    (h3 : y 3 ∈ Set.Ioo (-Real.pi) Real.pi)
    (h4 : y 4 ∈ Set.Ioo (-Real.pi) Real.pi) (h13 : y 1 ≠ y 3)
    (hz0 : 0 < dist (targetEndpointA y) (targetEndpointB y))
    (hz1 : dist (targetEndpointA y) (targetEndpointB y) < 1)
    (hD : targetCenter y ∈ LamC) : targetRegular y := by
  let p := targetEndpointA y
  let q := targetEndpointB y
  let D := targetCenter y
  have habs0 : |y 0| < 1 := abs_lt.mpr ⟨by linarith [h0.1],h0.2⟩
  have habs2 : |y 2| < 1 := abs_lt.mpr ⟨h2.1,by linarith [h2.2]⟩
  have hunit (h φ : ℝ) (hh : |h| < 1) : ‖endpointCylinder h φ‖ = 1 := by
    have hr : 0 ≤ 1-h^2 := by
      have hs := mul_self_lt_mul_self (abs_nonneg h) hh
      nlinarith [sq_abs h]
    have hn : ‖endpointCylinder h φ‖^2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [endpointCylinder,Fin.sum_univ_succ]
      simp [e,e1,e2,mul_pow,Real.sq_sqrt hr]
      nlinarith [congrArg (fun t : ℝ => (1-h^2)*t) (Real.sin_sq_add_cos_sq φ)]
    nlinarith [norm_nonneg (endpointCylinder h φ)]
  have hpunit : ‖p‖ = 1 := hunit _ _ habs0
  have hqdiff : q-e = endpointCylinder (y 2) (y 3) := by
    dsimp [q,targetEndpointB]
    abel
  have hqunit : ‖q-e‖ = 1 := by rw [hqdiff]; exact hunit _ _ habs2
  have hp0 : p 0 = y 0 := by simp [p,targetEndpointA,endpointCylinder,e,e1,e2]
  have hq0 : q 0 = 1+y 2 := by simp [q,targetEndpointB,endpointCylinder,e,e1,e2]
  have hip : inner ℝ p e = y 0 := by
    simpa [e,EuclideanSpace.inner_single_right] using hp0
  have hiq : inner ℝ q e = 1+y 2 := by
    simpa [e,EuclideanSpace.inner_single_right] using hq0
  have hpsq : ‖p-e‖^2 = 2-2*(y 0) := by
    rw [norm_sub_sq_real,hpunit,hip]
    norm_num [e]
    ring
  have hqsq : ‖q‖^2 = 2+2*(y 2) := by
    have h := norm_sub_sq_real q e
    rw [hqunit,hiq] at h
    norm_num [e] at h
    nlinarith
  have hpFA : p ∈ FA := by
    constructor
    · change dist p 0 = 1
      simpa only [dist_zero_right] using hpunit
    · change dist p e ≤ 1
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (p-e),h0.1]
  have hqFB : q ∈ FB := by
    constructor
    · change dist q e = 1
      simpa only [dist_eq_norm] using hqunit
    · change dist q 0 ≤ 1
      rw [dist_zero_right]
      nlinarith [norm_nonneg q,h2.2]
  have hf := target_centerFrame_nonzero y habs0 habs2 h1 h3 h13
  have hc := target_center_geometry y hz0 (by linarith) hf h4
  have hoff : offAxis D := contact_axis_exclusion D p q hD hpunit hqunit
    (by rw [hp0]; exact h0.1) (by rw [hq0]; linarith [h2.2]) hc.1 hc.2.1
  have hactive := contact_incidence_regular D p q hD hoff hpFA hqFB hc.1 hc.2.1 hz0
  exact ⟨hpFA,hqFB,habs0,habs2,h1,h3,h4,hz0,hz1,hD,hoff,hactive.1,hf,
    Complex.mem_slitPlane_iff.mpr (Or.inl hactive.2.1),
    Complex.mem_slitPlane_iff.mpr (Or.inl hactive.2.2)⟩
