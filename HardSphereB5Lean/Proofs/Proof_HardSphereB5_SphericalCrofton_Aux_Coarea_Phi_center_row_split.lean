import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_smooth
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_u_smooth
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_v_smooth
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_unitDir_smooth
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_A
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_B
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_contact_gradient
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
set_option maxHeartbeats 1800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_split
    (x : Chart5) (hreg : sourceRegular x)
    (hR : Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1) :
    ∃ LP LQ : Pt →L[ℝ] ℝ, ∀ w : Chart5,
      (fderiv ℝ Phi x w) 4 =
        (dist (sourceEndpointA x) (sourceEndpointB x) *
          (1-dist (sourceEndpointA x) (sourceEndpointB x)^2/4))⁻¹ *
          inner ℝ (cross (sourceEndpointA x-sourceCenter x) (sourceEndpointB x-sourceCenter x))
            (fderiv ℝ sourceCenter x w) +
        LP (fderiv ℝ sourceEndpointA x w) + LQ (fderiv ℝ sourceEndpointB x w) := by
  rcases hreg with ⟨hoff,hL,hpA,hpB,hz0,hz1,hθA,hθB,hp0,hq0,hf,hpa,hpb,hpc⟩
  have hD : sourceCenter x ≠ 0 := by
    intro h0
    exact hoff 0 (by simpa using h0)
  have hDe : sourceCenter x ≠ e := by
    intro he
    exact hoff 1 (by simpa using he)
  have hnormA : ‖sourceCenter x‖ ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall, dist_zero_right] using hL.1
  have hnormB : ‖sourceCenter x-e‖ ≤ 1 := by
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
  have hsmooth : ContDiffAt ℝ ⊤ Phi x :=
    HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_smooth x hD hDe (by linarith) (by linarith)
      hrawA hrawB hd hf hpa hpb hpc
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
        (HardSphereB5.SphericalCrofton.Aux.MovingArc.u_smooth (sourceCenter x) (x 3) hD (by linarith) hrawA)
        (hDsm.prodMk (hcoord 3))
    exact hDsm.add hu
  have hQ : ContDiffAt ℝ ⊤ sourceEndpointB x := by
    unfold sourceEndpointB
    have hv : ContDiffAt ℝ ⊤ (fun y : Chart5 =>
        HardSphereB5.SphericalCrofton.Aux.MovingArc.v (sourceCenter y) (y 4)) x :=
      ContDiffAt.comp (g := fun w : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.v w.1 w.2)
        (f := fun y : Chart5 => (sourceCenter y, y 4)) x
        (HardSphereB5.SphericalCrofton.Aux.MovingArc.v_smooth (sourceCenter x) (x 4) hDe (by linarith) hrawB)
        (hDsm.prodMk (hcoord 4))
    exact hDsm.add hv
  let D : Pt := sourceCenter x
  let p : Pt := sourceEndpointA x
  let q : Pt := sourceEndpointB x
  let E := Pt × (Pt × Pt)
  let T : E := (D,(p,q))
  let H : E → ℝ := fun y => Complex.arg (centerPhase y.1 y.2.1 y.2.2)
  have hP0 : ContDiffAt ℝ ⊤ (fun y : E => y.2.1) T :=
    ContDiffAt.comp (g := fun z : Pt × Pt => z.1) (f := fun y : E => y.2) T
      contDiffAt_fst contDiffAt_snd
  have hQ0 : ContDiffAt ℝ ⊤ (fun y : E => y.2.2) T :=
    ContDiffAt.comp (g := fun z : Pt × Pt => z.2) (f := fun y : E => y.2) T
      contDiffAt_snd contDiffAt_snd
  have hcross (f g : E → Pt) (hf : ContDiffAt ℝ ⊤ f T)
      (hg : ContDiffAt ℝ ⊤ g T) :
      ContDiffAt ℝ ⊤ (fun y => cross (f y) (g y)) T := by
    unfold cross
    apply PiLp.contDiff_toLp.contDiffAt.comp
    apply contDiffAt_pi.2
    have h1 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => f y i) T :=
      (contDiffAt_piLp 2).mp hf i
    have h2 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => g y i) T :=
      (contDiffAt_piLp 2).mp hg i
    intro i
    fin_cases i
    · change ContDiffAt ℝ ⊤ (fun y => f y 1 * g y 2 - f y 2 * g y 1) T
      exact ((h1 1).mul (h2 2)).sub ((h1 2).mul (h2 1))
    · change ContDiffAt ℝ ⊤ (fun y => f y 2 * g y 0 - f y 0 * g y 2) T
      exact ((h1 2).mul (h2 0)).sub ((h1 0).mul (h2 2))
    · change ContDiffAt ℝ ⊤ (fun y => f y 0 * g y 1 - f y 1 * g y 0) T
      exact ((h1 0).mul (h2 1)).sub ((h1 1).mul (h2 0))
  have hsep : ContDiffAt ℝ ⊤ (fun y : E => y.2.2-y.2.1) T := hQ0.sub hP0
  have hN : ContDiffAt ℝ ⊤ (fun y : E => unitDir (y.2.2-y.2.1)) T :=
    ContDiffAt.comp (g := unitDir) (f := fun y : E => y.2.2-y.2.1) T
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.unitDir_smooth _ hd) hsep
  let raw : E → Pt := fun y => e - (inner ℝ (unitDir (y.2.2-y.2.1)) e) • unitDir (y.2.2-y.2.1)
  have hraw : ContDiffAt ℝ ⊤ raw T := contDiffAt_const.sub ((hN.inner ℝ contDiffAt_const).smul hN)
  have hraw0 : raw T ≠ 0 := by
    intro h0
    apply hf
    change unitDir (raw T) = 0
    simp [unitDir,h0]
  have hF0 : ContDiffAt ℝ ⊤ (fun y : E => centerFrame0 (y.2.2-y.2.1)) T := by
    change ContDiffAt ℝ ⊤ (fun y => unitDir (raw y)) T
    exact ContDiffAt.comp (g := unitDir) (f := raw) T
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.unitDir_smooth _ hraw0) hraw
  have hF1 : ContDiffAt ℝ ⊤ (fun y : E => centerFrame1 (y.2.2-y.2.1)) T :=
    hcross _ _ hN hF0
  have hmid : ContDiffAt ℝ ⊤ (fun y : E => midpoint ℝ y.2.1 y.2.2) T := by
    simpa only [midpoint_eq_smul_add] using (hP0.add hQ0).const_smul (⅟2 : ℝ)
  have hdisp : ContDiffAt ℝ ⊤ (fun y : E => y.1-midpoint ℝ y.2.1 y.2.2) T :=
    contDiffAt_fst.sub hmid
  have hphase (f g : E → ℝ) (hf : ContDiffAt ℝ ⊤ f T) (hg : ContDiffAt ℝ ⊤ g T) :
      ContDiffAt ℝ ⊤ (fun y => phase (f y) (g y)) T := by
    have hrepr (a b : ℝ) : phase a b = (a : ℂ)+(b : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [phase]
    simp_rw [hrepr]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp T hf).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp T hg).mul contDiffAt_const)
  have hph : ContDiffAt ℝ ⊤ (fun y : E => centerPhase y.1 y.2.1 y.2.2) T :=
    hphase _ _ (hF0.inner ℝ hdisp) (hF1.inner ℝ hdisp)
  have hlog : ContDiffAt ℝ ⊤ (fun y : E => Complex.log (centerPhase y.1 y.2.1 y.2.2)) T :=
    ContDiffAt.comp (g := Complex.log) (f := fun y : E => centerPhase y.1 y.2.1 y.2.2) T
      ((Complex.contDiffAt_log hpc).restrict_scalars ℝ) hph
  have hH : ContDiffAt ℝ ⊤ H T := by
    have him : ContDiffAt ℝ ⊤ (fun y : E => (Complex.log (centerPhase y.1 y.2.1 y.2.2)).im) T :=
      ContDiffAt.comp (g := fun z : ℂ => z.im) (f := fun y : E => Complex.log (centerPhase y.1 y.2.1 y.2.2)) T
        Complex.imCLM.contDiff.contDiffAt hlog
    simpa only [Complex.log_im] using him
  let L : E →L[ℝ] ℝ := fderiv ℝ H T
  let ID : Pt →L[ℝ] E := ContinuousLinearMap.inl ℝ Pt (Pt × Pt)
  let IP : Pt →L[ℝ] E := (ContinuousLinearMap.inr ℝ Pt (Pt × Pt)).comp (ContinuousLinearMap.inl ℝ Pt Pt)
  let IQ : Pt →L[ℝ] E := (ContinuousLinearMap.inr ℝ Pt (Pt × Pt)).comp (ContinuousLinearMap.inr ℝ Pt Pt)
  let LP : Pt →L[ℝ] ℝ := L.comp IP
  let LQ : Pt →L[ℝ] ℝ := L.comp IQ
  let C : Pt →L[ℝ] ℝ := (dist p q*(1-dist p q^2/4))⁻¹ • (innerSL ℝ (cross (p-D) (q-D)))
  have hDp : dist D p = 1 := by
    rw [dist_comm,dist_eq_norm]
    simpa [D,p,sourceEndpointA] using
      (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A (sourceCenter x) hoff (by linarith) (x 3)).1
  have hDq : dist D q = 1 := by
    rw [dist_comm,dist_eq_norm]
    simpa [D,q,sourceEndpointB] using
      (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_B (sourceCenter x) hoff (by linarith) (x 4)).1
  have hID : L.comp ID = C := by
    have ht : HasFDerivAt (fun W : Pt => H (W,(p,q))) (L.comp ID) D :=
      HasFDerivAt.comp (g := H) (f := fun W : Pt => (W,(p,q))) D
        ((hH.differentiableAt (by simp)).hasFDerivAt) (hasFDerivAt_prodMk_left D (p,q))
    exact ht.unique (HardSphereB5.SphericalCrofton.Aux.Coarea.center_phase_contact_gradient D p q
      hz0 (by linarith) hDp hDq hf hpc)
  let JS : Chart5 →L[ℝ] E := (fderiv ℝ sourceCenter x).prod
    ((fderiv ℝ sourceEndpointA x).prod (fderiv ℝ sourceEndpointB x))
  have hchain : HasFDerivAt (fun y : Chart5 => H (sourceCenter y,(sourceEndpointA y,sourceEndpointB y)))
      (L.comp JS) x :=
    HasFDerivAt.comp (g := H)
      (f := fun y : Chart5 => (sourceCenter y,(sourceEndpointA y,sourceEndpointB y))) x
      ((hH.differentiableAt (by simp)).hasFDerivAt)
      ((hDsm.differentiableAt (by simp)).hasFDerivAt.prodMk
        ((hP.differentiableAt (by simp)).hasFDerivAt.prodMk (hQ.differentiableAt (by simp)).hasFDerivAt))
  have heq : (fun y : Chart5 => (Phi y) 4) =
      (fun y : Chart5 => H (sourceCenter y,(sourceEndpointA y,sourceEndpointB y))) := by
    funext y
    simp [Phi,pack5,H,EuclideanSpace.single_apply]
  let E4 : Chart5 →L[ℝ] ℝ := @EuclideanSpace.proj (Fin 5) ℝ _ 4
  have he4 : HasFDerivAt (fun y : Chart5 => y 4) E4 (Phi x) := by
    change HasFDerivAt E4 E4 (Phi x)
    exact E4.hasFDerivAt
  have hcoordder : HasFDerivAt (fun y : Chart5 => (Phi y) 4)
      (E4.comp (fderiv ℝ Phi x)) x :=
    HasFDerivAt.comp (g := fun y : Chart5 => y 4) (f := Phi) x
      he4 (hsmooth.differentiableAt (by simp)).hasFDerivAt
  rw [heq] at hcoordder
  have hj : E4.comp (fderiv ℝ Phi x) = L.comp JS :=
    hcoordder.unique hchain
  refine ⟨LP,LQ,?_⟩
  intro w
  have hsplit : JS w = ID (fderiv ℝ sourceCenter x w)+
      IP (fderiv ℝ sourceEndpointA x w)+IQ (fderiv ℝ sourceEndpointB x w) := by
    change (fderiv ℝ sourceCenter x w,(fderiv ℝ sourceEndpointA x w,fderiv ℝ sourceEndpointB x w)) =
      (fderiv ℝ sourceCenter x w + 0 + 0,
        (0 + fderiv ℝ sourceEndpointA x w + 0, 0 + 0 + fderiv ℝ sourceEndpointB x w))
    simp only [add_zero,zero_add]
  have h := congrArg (fun K : Chart5 →L[ℝ] ℝ => K w) hj
  change (fderiv ℝ Phi x w) 4 = L (JS w) at h
  rw [hsplit,map_add,map_add] at h
  have hid : L (ID (fderiv ℝ sourceCenter x w)) = C (fderiv ℝ sourceCenter x w) :=
    congrArg (fun K : Pt →L[ℝ] ℝ => K (fderiv ℝ sourceCenter x w)) hID
  rw [hid] at h
  exact h

