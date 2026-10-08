import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_arg_inverse
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section

private theorem phase_eq (a b : ℝ) : phase a b = (a : ℂ) + Complex.I * (b : ℂ) := by
  apply Complex.ext <;> simp [phase]

private theorem cylinder_inverse (p : Pt) (hp : ‖p‖ = 1) (h0 : |p 0| < 1) :
    endpointCylinder (p 0) (azimuth p) = p := by
  unfold endpointCylinder azimuth
  rw [phase_eq]
  exact HardSphereB5.SphericalCrofton.Aux.Coarea.endpoint_arg_inverse p hp h0

private theorem pack_proj (a b c d f : ℝ) (i : Fin 5) :
    pack5 a b c d f i = ![a,b,c,d,f] i := by
  fin_cases i <;> simp [pack5, PiLp.single_apply]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_endpoints (x : Chart5) (hA : sourceEndpointA x ∈ FA) (hB : sourceEndpointB x ∈ FB)
    (hp : |sourceEndpointA x 0| < 1) (hp' : |sourceEndpointB x 0 - 1| < 1) :
    targetEndpointA (Phi x) = sourceEndpointA x ∧
      targetEndpointB (Phi x) = sourceEndpointB x := by
  let p := sourceEndpointA x
  let p' := sourceEndpointB x
  have hpn : ‖p‖ = 1 := by simpa [FA, Metric.mem_sphere, dist_zero_right] using hA.1
  have hp'n : ‖p'-e‖ = 1 := by simpa [FB, Metric.mem_sphere, dist_eq_norm] using hB.1
  have haxis : p' 0 - 1 = (p'-e) 0 := by simp [e]
  have haz : azimuth p' = azimuth (p'-e) := by simp [azimuth, e]
  constructor
  · change endpointCylinder ((Phi x) 0) ((Phi x) 1) = p
    simp [Phi, pack_proj, Matrix.cons_val_zero, Matrix.cons_val_succ]
    exact cylinder_inverse p hpn hp
  · change e + endpointCylinder ((Phi x) 2) ((Phi x) 3) = p'
    simp [Phi, pack_proj, Matrix.cons_val_zero, Matrix.cons_val_succ]
    have hp0 : |(p'-e) 0| < 1 := by simpa [p', e] using hp'
    rw [haxis, haz, cylinder_inverse (p'-e) hp'n hp0]
    abel
