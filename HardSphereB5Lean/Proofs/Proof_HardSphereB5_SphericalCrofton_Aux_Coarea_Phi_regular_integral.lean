import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_injOn_regular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_jacobian
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_smooth
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_regular_integral (S : Set Chart5)
    (hS : ∀ x ∈ S, sourceRegular x ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)))
    (hSm : MeasurableSet S) (g : Chart5 → ℝ) :
    (∫ y in Phi '' S, g y) =
      ∫ x in S, (dist (sourceEndpointA x) (sourceEndpointB x) /
        (‖sourceCenter x‖ * ‖sourceCenter x-e‖)) * g (Phi x)  := by
  have hder (x : Chart5) (hx : x ∈ S) : HasFDerivAt Phi (fderiv ℝ Phi x) x := by
    rcases hS x hx with ⟨hreg,hR,hα,hβ⟩
    rcases hreg with ⟨hoff,hL,hpA,hpB,hz0,hz1,hθA,hθB,hp0,hq0,hf,hpa,hpb,hpc⟩
    have hD : sourceCenter x ≠ 0 := by
      intro h0; exact hoff 0 (by simpa using h0)
    have hDe : sourceCenter x ≠ e := by
      intro he; exact hoff 1 (by simpa using he)
    have hnA : ‖sourceCenter x‖ ≤ 1 := by
      simpa [LamC, Metric.mem_closedBall, dist_zero_right] using hL.1
    have hnB : ‖sourceCenter x-e‖ ≤ 1 := by
      simpa [LamC, Metric.mem_closedBall, dist_eq_norm] using hL.2
    have hE := HardSphereB5.SphericalCrofton.Aux.MovingArc.EA_orthonormal (sourceCenter x) hoff
    have hBg := HardSphereB5.SphericalCrofton.Aux.MovingArc.B_chart_geometry (sourceCenter x) hL hoff hR
    have hrawA : rawA (sourceCenter x) ≠ 0 := by
      intro hz
      have h := hE.norm_eq_one (0 : Fin 2)
      simp [EA, unitDir, hz] at h
    have hrawB : rawB (sourceCenter x) ≠ 0 := by
      intro hz
      have h := hBg.1.norm_eq_one (0 : Fin 2)
      simp [EB, unitDir, hz] at h
    have hd : sourceEndpointB x-sourceEndpointA x ≠ 0 := by
      intro he
      have heq := sub_eq_zero.mp he
      rw [heq, dist_self] at hz0
      exact (lt_irrefl 0) hz0
    have hsm := HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_smooth x hD hDe
      (by linarith) (by linarith) hrawA hrawB hd hf hpa hpb hpc
    exact (hsm.differentiableAt (by simp)).hasFDerivAt
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure Chart5) hSm
    (fun x hx => (hder x hx).hasFDerivWithinAt)
    (HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_injOn_regular S hS) g
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hSm] with x hx
  rcases hS x hx with ⟨hreg,hR,hα,hβ⟩
  rw [HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_jacobian x hreg hR hα hβ]
  rfl

