import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_axis_exclusion
    (D p q : Pt) (hD : D ∈ LamC) (hp : ‖p‖ = 1) (hq : ‖q-e‖ = 1)
    (hp0 : 1/2 < p 0) (hq0 : q 0 < 1/2)
    (hDp : dist D p = 1) (hDq : dist D q = 1) : offAxis D := by
  intro t ht
  have hDn : ‖D‖ ≤ 1 := by simpa [LamC,Metric.mem_closedBall,dist_zero_right] using hD.1
  have hDen : ‖D-e‖ ≤ 1 := by simpa [LamC,Metric.mem_closedBall,dist_eq_norm] using hD.2
  have htA : |t| ≤ 1 := by simpa [ht,norm_smul,e] using hDn
  have hte : D-e = (t-1) • e := by rw [ht]; module
  have htB : |t-1| ≤ 1 := by rw [hte] at hDen; simpa [norm_smul,e] using hDen
  have ht0 : 0 ≤ t := by linarith [(abs_le.mp htB).1]
  have ht1 : t ≤ 1 := (abs_le.mp htA).2
  have hsA : t * (t-2*(p 0)) = 0 := by
    have h := norm_sub_sq_real D p
    rw [← dist_eq_norm,hDp,hp,ht] at h
    simp [norm_smul,real_inner_smul_left,e,EuclideanSpace.inner_single_left] at h
    nlinarith [sq_abs t]
  have htz : t = 0 := by
    rcases mul_eq_zero.mp hsA with h | h
    · exact h
    · linarith
  have hinner : inner ℝ e (q-e) = q 0-1 := by simp [inner_sub_right,e,EuclideanSpace.inner_single_left]
  have hnorm : ‖(D-e)-(q-e)‖ = 1 := by
    convert hDq using 1
    rw [dist_eq_norm]
    congr 1
    abel
  have hsB : (t-1) * (t-1-2*(q 0-1)) = 0 := by
    have h := norm_sub_sq_real (D-e) (q-e)
    rw [hnorm,hq,hte,real_inner_smul_left,hinner] at h
    simp [norm_smul,e] at h
    nlinarith [sq_abs (t-1)]
  rcases mul_eq_zero.mp hsB with h | h <;> linarith
