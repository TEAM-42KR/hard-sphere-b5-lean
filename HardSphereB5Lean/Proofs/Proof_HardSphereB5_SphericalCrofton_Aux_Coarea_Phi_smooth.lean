import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_u_smooth
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_v_smooth
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_unitDir_smooth
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
set_option maxHeartbeats 1500000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_smooth (x : Chart5)
    (hD : sourceCenter x ≠ 0) (hDe : sourceCenter x ≠ e)
    (hrA : ‖sourceCenter x‖ < 2) (hrB : ‖sourceCenter x - e‖ < 2)
    (hA : HardSphereB5.SphericalCrofton.Aux.MovingArc.rawA (sourceCenter x) ≠ 0)
    (hB : HardSphereB5.SphericalCrofton.Aux.MovingArc.rawB (sourceCenter x) ≠ 0)
    (hd : sourceEndpointB x - sourceEndpointA x ≠ 0)
    (hf : centerFrame0 (sourceEndpointB x - sourceEndpointA x) ≠ 0)
    (hphaseA : phase ((sourceEndpointA x) 1) ((sourceEndpointA x) 2) ∈ Complex.slitPlane)
    (hphaseB : phase ((sourceEndpointB x) 1) ((sourceEndpointB x) 2) ∈ Complex.slitPlane)
    (hphaseC : centerPhase (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) ∈ Complex.slitPlane) :
    ContDiffAt ℝ ⊤ Phi x := by
  have hcoord (i : Fin 5) : ContDiffAt ℝ ⊤ (fun y : Chart5 => y i) x :=
    (contDiffAt_piLp 2).mp contDiffAt_id i
  have hDsm : ContDiffAt ℝ ⊤ sourceCenter x := by
    unfold sourceCenter
    exact (((hcoord 0).smul contDiffAt_const).add
      ((hcoord 1).smul contDiffAt_const)).add ((hcoord 2).smul contDiffAt_const)
  have hP : ContDiffAt ℝ ⊤ sourceEndpointA x := by
    unfold sourceEndpointA
    have hu : ContDiffAt ℝ ⊤ (fun y : Chart5 =>
        HardSphereB5.SphericalCrofton.Aux.MovingArc.u (sourceCenter y) (y 3)) x :=
      ContDiffAt.comp (g := fun w : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.u w.1 w.2)
        (f := fun y : Chart5 => (sourceCenter y, y 3)) x
        (HardSphereB5.SphericalCrofton.Aux.MovingArc.u_smooth (sourceCenter x) (x 3) hD hrA hA)
        (hDsm.prodMk (hcoord 3))
    exact hDsm.add hu
  have hQ : ContDiffAt ℝ ⊤ sourceEndpointB x := by
    unfold sourceEndpointB
    have hv : ContDiffAt ℝ ⊤ (fun y : Chart5 =>
        HardSphereB5.SphericalCrofton.Aux.MovingArc.v (sourceCenter y) (y 4)) x :=
      ContDiffAt.comp (g := fun w : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.v w.1 w.2)
        (f := fun y : Chart5 => (sourceCenter y, y 4)) x
        (HardSphereB5.SphericalCrofton.Aux.MovingArc.v_smooth (sourceCenter x) (x 4) hDe hrB hB)
        (hDsm.prodMk (hcoord 4))
    exact hDsm.add hv
  have hpc (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => sourceEndpointA y i) x :=
    (contDiffAt_piLp 2).mp hP i
  have hqc (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => sourceEndpointB y i) x :=
    (contDiffAt_piLp 2).mp hQ i
  have hcross (f g : Chart5 → Pt) (hf : ContDiffAt ℝ ⊤ f x)
      (hg : ContDiffAt ℝ ⊤ g x) :
      ContDiffAt ℝ ⊤ (fun y => cross (f y) (g y)) x := by
    unfold cross
    apply PiLp.contDiff_toLp.contDiffAt.comp
    apply contDiffAt_pi.2
    have h1 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => f y i) x :=
      (contDiffAt_piLp 2).mp hf i
    have h2 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => g y i) x :=
      (contDiffAt_piLp 2).mp hg i
    intro i
    fin_cases i
    · change ContDiffAt ℝ ⊤ (fun y => f y 1 * g y 2 - f y 2 * g y 1) x
      exact ((h1 1).mul (h2 2)).sub ((h1 2).mul (h2 1))
    · change ContDiffAt ℝ ⊤ (fun y => f y 2 * g y 0 - f y 0 * g y 2) x
      exact ((h1 2).mul (h2 0)).sub ((h1 0).mul (h2 2))
    · change ContDiffAt ℝ ⊤ (fun y => f y 0 * g y 1 - f y 1 * g y 0) x
      exact ((h1 0).mul (h2 1)).sub ((h1 1).mul (h2 0))
  have hsep : ContDiffAt ℝ ⊤ (fun y => sourceEndpointB y - sourceEndpointA y) x :=
    hQ.sub hP
  have hN : ContDiffAt ℝ ⊤ (fun y => unitDir (sourceEndpointB y - sourceEndpointA y)) x :=
    ContDiffAt.comp (g := unitDir)
      (f := fun y : Chart5 => sourceEndpointB y - sourceEndpointA y) x
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.unitDir_smooth _ hd) hsep
  let raw : Chart5 → Pt := fun y => e -
    (inner ℝ (unitDir (sourceEndpointB y - sourceEndpointA y)) e) •
      unitDir (sourceEndpointB y - sourceEndpointA y)
  have hraw : ContDiffAt ℝ ⊤ raw x :=
    contDiffAt_const.sub ((hN.inner ℝ contDiffAt_const).smul hN)
  have hraw0 : raw x ≠ 0 := by
    intro h0
    apply hf
    change unitDir (raw x) = 0
    simp [unitDir, h0]
  have hF0 : ContDiffAt ℝ ⊤
      (fun y => centerFrame0 (sourceEndpointB y - sourceEndpointA y)) x := by
    change ContDiffAt ℝ ⊤ (fun y => unitDir (raw y)) x
    exact ContDiffAt.comp (g := unitDir) (f := raw) x
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.unitDir_smooth _ hraw0) hraw
  have hF1 : ContDiffAt ℝ ⊤
      (fun y => centerFrame1 (sourceEndpointB y - sourceEndpointA y)) x := by
    exact hcross _ _ hN hF0
  have hmid : ContDiffAt ℝ ⊤
      (fun y => midpoint ℝ (sourceEndpointA y) (sourceEndpointB y)) x := by
    simpa only [midpoint_eq_smul_add] using (hP.add hQ).const_smul (⅟2 : ℝ)
  have hdisp : ContDiffAt ℝ ⊤
      (fun y => sourceCenter y - midpoint ℝ (sourceEndpointA y) (sourceEndpointB y)) x :=
    hDsm.sub hmid
  have hphase (f g : Chart5 → ℝ) (hf : ContDiffAt ℝ ⊤ f x)
      (hg : ContDiffAt ℝ ⊤ g x) :
      ContDiffAt ℝ ⊤ (fun y => phase (f y) (g y)) x := by
    have hrepr (a b : ℝ) : phase a b = (a : ℂ) + (b : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [phase]
    simp_rw [hrepr]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hf).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hg).mul contDiffAt_const)
  have hphase0 : ContDiffAt ℝ ⊤
      (fun y => phase (sourceEndpointA y 1) (sourceEndpointA y 2)) x :=
    hphase _ _ (hpc 1) (hpc 2)
  have hphase1 : ContDiffAt ℝ ⊤
      (fun y => phase (sourceEndpointB y 1) (sourceEndpointB y 2)) x :=
    hphase _ _ (hqc 1) (hqc 2)
  have hphase2 : ContDiffAt ℝ ⊤
      (fun y => centerPhase (sourceCenter y) (sourceEndpointA y) (sourceEndpointB y)) x :=
    hphase _ _ (hF0.inner ℝ hdisp) (hF1.inner ℝ hdisp)
  have harg (f : Chart5 → ℂ) (hf : ContDiffAt ℝ ⊤ f x)
      (hs : f x ∈ Complex.slitPlane) : ContDiffAt ℝ ⊤ (fun y => Complex.arg (f y)) x := by
    have hlog : ContDiffAt ℝ ⊤ (fun y => Complex.log (f y)) x :=
      ContDiffAt.comp (g := Complex.log) (f := f) x
        ((Complex.contDiffAt_log hs).restrict_scalars ℝ) hf
    have him : ContDiffAt ℝ ⊤ (fun y => (Complex.log (f y)).im) x :=
      ContDiffAt.comp (g := fun z : ℂ => z.im) (f := fun y => Complex.log (f y)) x
        Complex.imCLM.contDiff.contDiffAt hlog
    simpa only [Complex.log_im] using him
  have harg0 : ContDiffAt ℝ ⊤ (fun y => azimuth (sourceEndpointA y)) x :=
    harg _ hphase0 hphaseA
  have harg1 : ContDiffAt ℝ ⊤ (fun y => azimuth (sourceEndpointB y)) x :=
    harg _ hphase1 hphaseB
  have harg2 : ContDiffAt ℝ ⊤
      (fun y => Complex.arg (centerPhase (sourceCenter y) (sourceEndpointA y) (sourceEndpointB y))) x :=
    harg _ hphase2 hphaseC
  unfold Phi pack5
  dsimp only
  exact (((((hpc 0).smul contDiffAt_const).add (harg0.smul contDiffAt_const)).add
    (((hqc 0).sub contDiffAt_const).smul contDiffAt_const)).add
      (harg1.smul contDiffAt_const)).add (harg2.smul contDiffAt_const)

