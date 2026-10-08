import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_endpoints
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_arg_inverse
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_arcA_image
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
set_option maxHeartbeats 700000

private theorem circle_phase (f : Fin 2 → Pt) (hf : Orthonormal ℝ f)
    (c : Pt) (r : ℝ) (hr : 0 < r) (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg (phase (inner ℝ (f 0) (circlePt c (f 0) (f 1) r θ-c))
      (inner ℝ (f 1) (circlePt c (f 0) (f 1) r θ-c))) = θ := by
  have hi := (orthonormal_iff_ite.mp hf)
  have hn (i : Fin 2) : ‖f i‖ = 1 := hf.norm_eq_one i
  have hp : phase (inner ℝ (f 0) (circlePt c (f 0) (f 1) r θ-c))
      (inner ℝ (f 1) (circlePt c (f 0) (f 1) r θ-c)) =
      (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp [phase, circlePt, inner_add_right, real_inner_smul_right, hi, hn, mul_add,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hp]
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
    (Complex.arg_mul_cos_add_sin_mul_I hr hθ)

private theorem pack_proj (a b c d f : ℝ) (i : Fin 5) :
    pack5 a b c d f i = ![a,b,c,d,f] i := by
  fin_cases i <;> simp [pack5, PiLp.single_apply]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Psi_Phi_arc (x : Chart5) (hreg : sourceRegular x)
    (hR : Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1)
    (hα : x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)))
    (hβ : x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x))) :
    Psi (Phi x) = x := by
  let D := sourceCenter x
  let p := sourceEndpointA x
  let p' := sourceEndpointB x
  rcases hreg with ⟨hoff,hL,hpFA,hpFB,hz0,hz1,hα0,hβ0,hpoleA,hpoleB,hframe,hcutA,hcutB,hcutC⟩
  have hD0 : D ≠ 0 := by intro h; exact hoff 0 (by simpa [D] using h)
  have hDe : D ≠ e := by intro h; exact hoff 1 (by simpa [D] using h)
  have hu : u D (x 3) ∈ arcA D := by
    rw [HardSphereB5.SphericalCrofton.Aux.MovingArc.arcA_image D hL hoff hR]
    exact ⟨x 3,hα,rfl⟩
  have hBg := HardSphereB5.SphericalCrofton.Aux.MovingArc.B_chart_geometry D hL hoff hR
  have hv : v D (x 4) ∈ arcB D := by
    rw [hBg.2.2.2.2.1]
    exact ⟨x 4,hβ,rfl⟩
  have hun : ‖u D (x 3)‖ = 1 := by
    have hh := hu
    rw [arcA, if_neg hD0] at hh
    exact hh.1.1
  have hvn : ‖v D (x 4)‖ = 1 := by
    have hh := hv
    rw [arcB, if_neg hDe] at hh
    exact hh.1.1
  have hdistA : dist D p = 1 := by
    change dist D (D+u D (x 3)) = 1
    rw [dist_eq_norm, show D-(D+u D (x 3)) = -u D (x 3) by abel, norm_neg, hun]
  have hdistB : dist D p' = 1 := by
    change dist D (D+v D (x 4)) = 1
    rw [dist_eq_norm, show D-(D+v D (x 4)) = -v D (x 4) by abel, norm_neg, hvn]
  have hend := HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_endpoints x hpFA hpFB hpoleA hpoleB
  have hcenter : targetCenter (Phi x) = D := by
    unfold targetCenter
    rw [hend.1,hend.2]
    have hpsi : (Phi x) 4 = Complex.arg (centerPhase D p p') := by
      simp [Phi, pack_proj, D,p,p']
    rw [hpsi]
    exact HardSphereB5.SphericalCrofton.Aux.Coarea.center_arg_inverse D p p' hz0 (by linarith) hdistA hdistB hframe
  have hradA : 0 < rA D := by
    have hn : ‖D‖ ≤ 1 := by simpa [LamC, Metric.mem_closedBall, dist_zero_right] using hL.1
    have hr : 0 < 1-‖D‖^2/4 := by nlinarith [norm_nonneg D]
    exact Real.sqrt_pos.mpr hr
  have hphaseA : Complex.arg (sourcePhaseA D p) = x 3 := by
    have hvec : p-D-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D =
        u D (x 3)-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D := by change D+u D (x 3)-D-_ = _; abel
    unfold sourcePhaseA
    rw [hvec]
    exact circle_phase (EA D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.EA_orthonormal D hoff)
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) (rA D) hradA (x 3) ⟨hα0.1,hα0.2.le⟩
  have hphaseB : Complex.arg (sourcePhaseB D p') = x 4 := by
    have hvec : p'-D-HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D =
        v D (x 4)-HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D := by change D+v D (x 4)-D-_ = _; abel
    unfold sourcePhaseB
    rw [hvec]
    exact circle_phase (EB D) hBg.1 (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D) (rB D)
      hBg.2.1 (x 4) ⟨hβ0.1,hβ0.2.le⟩
  unfold Psi
  rw [hcenter, hend.1,hend.2]
  change pack5 (D 0) (D 1) (D 2) (Complex.arg (sourcePhaseA D p))
    (Complex.arg (sourcePhaseB D p')) = x
  rw [hphaseA,hphaseB]
  ext i
  rw [pack_proj]
  fin_cases i <;> simp [D, sourceCenter, e,e1,e2, PiLp.single_apply]
