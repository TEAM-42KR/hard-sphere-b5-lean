import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_center_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_Psi_geometry
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
set_option maxHeartbeats 900000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_Psi_regular (y : Chart5) (hy : targetRegular y) :
    Phi (Psi y) = y ∧ sourceRegular (Psi y) ∧
    Rc ‖sourceCenter (Psi y)‖ ‖sourceCenter (Psi y)-e‖ < 1 ∧
    (Psi y) 3 ∈ Set.Icc (-(halfA (sourceCenter (Psi y)))) (halfA (sourceCenter (Psi y))) ∧
    (Psi y) 4 ∈ Set.Icc (-(halfB (sourceCenter (Psi y)))) (halfB (sourceCenter (Psi y))) := by
  have hg := target_Psi_geometry y hy
  rcases hy with ⟨hpFA,hpFB,hheightA,hheightB,hangleA,hangleB,hangleC,hz0,hz1,
    hL,hoff,hR,hframe,hsourcePhaseA,hsourcePhaseB⟩
  let p := targetEndpointA y
  let p' := targetEndpointB y
  let D := targetCenter y
  have hcenter := target_center_geometry y hz0 (by linarith) hframe hangleC
  have hpolar (r θ : ℝ) (hr : 0 < r) (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) :
      Complex.arg (phase (r * Real.cos θ) (r * Real.sin θ)) = θ ∧
      phase (r * Real.cos θ) (r * Real.sin θ) ∈ Complex.slitPlane := by
    have hp : phase (r * Real.cos θ) (r * Real.sin θ) =
        (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
      apply Complex.ext <;>
        simp only [phase,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
          Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
          mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
    have ha : Complex.arg (phase (r * Real.cos θ) (r * Real.sin θ)) = θ := by
      rw [hp]
      simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
        Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1,hθ.2.le⟩
    refine ⟨ha,Complex.mem_slitPlane_iff_arg.mpr ⟨?_,?_⟩⟩
    · rw [ha]
      exact ne_of_lt hθ.2
    · intro hz
      have hcos : r * Real.cos θ = 0 := by
        have hh := congrArg Complex.re hz
        exact hh
      have hsin : r * Real.sin θ = 0 := by
        have hh := congrArg Complex.im hz
        exact hh
      have hc := (mul_eq_zero.mp hcos).resolve_left (ne_of_gt hr)
      have hs := (mul_eq_zero.mp hsin).resolve_left (ne_of_gt hr)
      have hh := Real.sin_sq_add_cos_sq θ
      rw [hc,hs] at hh
      norm_num at hh
  have hrad (h : ℝ) (hh : |h| < 1) : 0 < Real.sqrt (1-h^2) := by
    apply Real.sqrt_pos.mpr
    have hs := mul_self_lt_mul_self (abs_nonneg h) hh
    nlinarith [sq_abs h]
  have hAphase : phase (p 1) (p 2) =
      phase (Real.sqrt (1-(y 0)^2) * Real.cos (y 1))
        (Real.sqrt (1-(y 0)^2) * Real.sin (y 1)) := by
    simp [p,targetEndpointA,endpointCylinder,e,e1,e2]
  have hBphase : phase (p' 1) (p' 2) =
      phase (Real.sqrt (1-(y 2)^2) * Real.cos (y 3))
        (Real.sqrt (1-(y 2)^2) * Real.sin (y 3)) := by
    simp [p',targetEndpointB,endpointCylinder,e,e1,e2]
  have hargA : azimuth p = y 1 := by
    unfold azimuth
    rw [hAphase]
    exact (hpolar _ _ (hrad _ hheightA) hangleA).1
  have hargB : azimuth p' = y 3 := by
    unfold azimuth
    rw [hBphase]
    exact (hpolar _ _ (hrad _ hheightB) hangleB).1
  have hp0 : p 0 = y 0 := by simp [p,targetEndpointA,endpointCylinder,e,e1,e2]
  have hp'0 : p' 0-1 = y 2 := by
    simp [p',targetEndpointB,endpointCylinder,e,e1,e2]
  have hPhi : Phi (Psi y) = y := by
    unfold Phi
    rw [hg.1,hg.2.1,hg.2.2.1]
    change pack5 (p 0) (azimuth p) (p' 0-1) (azimuth p')
      (Complex.arg (centerPhase D p p')) = y
    rw [hp0,hp'0,hargA,hargB,hcenter.2.2.1]
    ext i
    fin_cases i <;> simp [pack5]
  have hargSlit (z : ℂ) (hz : z ∈ Complex.slitPlane) :
      z.arg ∈ Set.Ioo (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg z,lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hz)⟩
  have hsource : sourceRegular (Psi y) := by
    unfold sourceRegular
    rw [hg.1,hg.2.1,hg.2.2.1]
    refine ⟨hoff,hL,hpFA,hpFB,hz0,hz1,?_,?_,?_,?_,hframe,?_,?_,hcenter.2.2.2⟩
    · simpa [Psi,pack5,D,p] using hargSlit (sourcePhaseA D p) hsourcePhaseA
    · simpa [Psi,pack5,D,p'] using hargSlit (sourcePhaseB D p') hsourcePhaseB
    · rw [hp0]
      exact hheightA
    · rw [hp'0]
      exact hheightB
    · rw [hAphase]
      exact (hpolar _ _ (hrad _ hheightA) hangleA).2
    · rw [hBphase]
      exact (hpolar _ _ (hrad _ hheightB) hangleB).2
  refine ⟨hPhi,hsource,?_,?_,?_⟩
  · rw [hg.1]
    exact hR
  · rw [hg.1]
    exact hg.2.2.2.1
  · rw [hg.1]
    exact hg.2.2.2.2
