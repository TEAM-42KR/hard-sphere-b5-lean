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
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_split
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_phase_fderiv
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
set_option maxHeartbeats 1800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_elimination
    (x : Chart5) (hreg : sourceRegular x)
    (hR : Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1) :
    ∃ k : Fin 4 → ℝ, ∀ w : Chart5,
      (fderiv ℝ Phi x w) 4 =
        (dist (sourceEndpointA x) (sourceEndpointB x) *
          (1-dist (sourceEndpointA x) (sourceEndpointB x)^2/4))⁻¹ *
          inner ℝ (cross (sourceEndpointA x-sourceCenter x) (sourceEndpointB x-sourceCenter x))
            (fderiv ℝ sourceCenter x w) +
        k 0 * (fderiv ℝ Phi x w) 0 + k 1 * (fderiv ℝ Phi x w) 1 +
        k 2 * (fderiv ℝ Phi x w) 2 + k 3 * (fderiv ℝ Phi x w) 3 := by
  have hreg0 := hreg
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
  let p : Pt := sourceEndpointA x
  let q : Pt := sourceEndpointB x
  let JP := fderiv ℝ sourceEndpointA x
  let JQ := fderiv ℝ sourceEndpointB x
  let J := fderiv ℝ Phi x
  have hoff_near : ∀ᶠ y in nhds x, offAxis (sourceCenter y) := by
    have hxy : (sourceCenter x) 1 ≠ 0 ∨ (sourceCenter x) 2 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hoff ((sourceCenter x) 0)
      ext i
      fin_cases i <;> simp [e,EuclideanSpace.single_apply,h.1,h.2]
    have hgood (Y : Pt) (hy : Y 1 ≠ 0 ∨ Y 2 ≠ 0) : offAxis Y := by
      intro t he
      rcases hy with h | h
      · have ht := congrArg (fun Z : Pt => Z 1) he
        simp [e,EuclideanSpace.single_apply] at ht
        exact h ht
      · have ht := congrArg (fun Z : Pt => Z 2) he
        simp [e,EuclideanSpace.single_apply] at ht
        exact h ht
    rcases hxy with h | h
    · have hn := ((contDiffAt_piLp 2).mp hDsm 1).continuousAt.eventually_ne h
      exact hn.mono (fun y hy => hgood (sourceCenter y) (Or.inl hy))
    · have hn := ((contDiffAt_piLp 2).mp hDsm 2).continuousAt.eventually_ne h
      exact hn.mono (fun y hy => hgood (sourceCenter y) (Or.inr hy))
  have hnearA : ∀ᶠ y in nhds x, ‖sourceCenter y‖ < 2 :=
    hDsm.continuousAt.norm.eventually_lt continuousAt_const (by linarith)
  have hnearB : ∀ᶠ y in nhds x, ‖sourceCenter y-e‖ < 2 :=
    (show ContinuousAt (fun y : Chart5 => ‖sourceCenter y-e‖) x from
      (hDsm.continuousAt.sub continuousAt_const).norm).eventually_lt
      (show ContinuousAt (fun _ : Chart5 => (2 : ℝ)) x from continuousAt_const) (by linarith)
  have hunitP : ∀ᶠ y in nhds x, ‖sourceEndpointA y‖ = 1 := by
    filter_upwards [hoff_near,hnearA] with y hy hr
    exact (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A (sourceCenter y) hy hr (y 3)).2
  have hunitQ : ∀ᶠ y in nhds x, ‖sourceEndpointB y-e‖ = 1 := by
    filter_upwards [hoff_near,hnearB] with y hy hr
    exact (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_B (sourceCenter y) hy hr (y 4)).2
  have htangent (F : Chart5 → Pt) (JF : Chart5 →L[ℝ] Pt)
      (hf : HasFDerivAt F JF x) (hu : ∀ᶠ y in nhds x, ‖F y‖ = 1) :
      ∀ w, inner ℝ (F x) (JF w) = 0 := by
    have he : (fun y => ‖F y‖^2) =ᶠ[nhds x] (fun _ => (1 : ℝ)) :=
      hu.mono (fun y hy => by change ‖F y‖^2 = 1; rw [hy]; norm_num)
    have hz : HasFDerivAt (fun y => ‖F y‖^2) (0 : Chart5 →L[ℝ] ℝ) x :=
      he.hasFDerivAt_iff.mpr (hasFDerivAt_const (1 : ℝ) x)
    have hmap := (hf.norm_sq).unique hz
    intro w
    have h := congrArg (fun L : Chart5 →L[ℝ] ℝ => L w) hmap
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      innerSL_apply_apply,smul_eq_mul,Pi.zero_apply] at h
    have ht : inner ℝ (F x) (JF w) + inner ℝ (F x) (JF w) = 0 := by
      simpa only [two_smul,ContinuousLinearMap.zero_apply] using h
    linarith
  have htP : ∀ w, inner ℝ p (JP w) = 0 :=
    htangent sourceEndpointA JP (hP.differentiableAt (by simp)).hasFDerivAt hunitP
  have htQ : ∀ w, inner ℝ (q-e) (JQ w) = 0 :=
    htangent (fun y => sourceEndpointB y-e) JQ
      ((hQ.differentiableAt (by simp)).hasFDerivAt.sub_const e) hunitQ
  have hprojP (i : Fin 3) : HasFDerivAt (fun y : Chart5 => sourceEndpointA y i)
      ((@EuclideanSpace.proj (Fin 3) ℝ _ i).comp JP) x := by
    let Ei : Pt →L[ℝ] ℝ := @EuclideanSpace.proj (Fin 3) ℝ _ i
    have he : HasFDerivAt (fun y : Pt => y i) Ei (sourceEndpointA x) := by
      change HasFDerivAt Ei Ei (sourceEndpointA x)
      exact Ei.hasFDerivAt
    exact HasFDerivAt.comp (g := fun y : Pt => y i) (f := sourceEndpointA) x
      he (hP.differentiableAt (by simp)).hasFDerivAt
  have hprojQ (i : Fin 3) : HasFDerivAt (fun y : Chart5 => sourceEndpointB y i)
      ((@EuclideanSpace.proj (Fin 3) ℝ _ i).comp JQ) x := by
    let Ei : Pt →L[ℝ] ℝ := @EuclideanSpace.proj (Fin 3) ℝ _ i
    have he : HasFDerivAt (fun y : Pt => y i) Ei (sourceEndpointB x) := by
      change HasFDerivAt Ei Ei (sourceEndpointB x)
      exact Ei.hasFDerivAt
    exact HasFDerivAt.comp (g := fun y : Pt => y i) (f := sourceEndpointB) x
      he (hQ.differentiableAt (by simp)).hasFDerivAt
  have hprojJ (i : Fin 5) : HasFDerivAt (fun y : Chart5 => Phi y i)
      ((@EuclideanSpace.proj (Fin 5) ℝ _ i).comp J) x := by
    let Ei : Chart5 →L[ℝ] ℝ := @EuclideanSpace.proj (Fin 5) ℝ _ i
    have he : HasFDerivAt (fun y : Chart5 => y i) Ei (Phi x) := by
      change HasFDerivAt Ei Ei (Phi x)
      exact Ei.hasFDerivAt
    exact HasFDerivAt.comp (g := fun y : Chart5 => y i) (f := Phi) x
      he (hsmooth.differentiableAt (by simp)).hasFDerivAt
  have hheightP (w) : J w 0 = JP w 0 := by
    have he : (fun y : Chart5 => Phi y 0) = (fun y => sourceEndpointA y 0) := by
      funext y; simp [Phi,pack5,EuclideanSpace.single_apply]
    have h := hprojJ 0
    rw [he] at h
    exact congrArg (fun L : Chart5 →L[ℝ] ℝ => L w) (h.unique (hprojP 0))
  have hheightQ (w) : J w 2 = JQ w 0 := by
    have he : (fun y : Chart5 => Phi y 2) = (fun y => sourceEndpointB y 0-1) := by
      funext y; simp [Phi,pack5,EuclideanSpace.single_apply]
    have h := hprojJ 2
    rw [he] at h
    have heq := h.unique ((hprojQ 0).sub_const 1)
    exact congrArg (fun L : Chart5 →L[ℝ] ℝ => L w) heq
  let RP : ℝ := p 1^2+p 2^2
  let RQ : ℝ := q 1^2+q 2^2
  have hRP : RP ≠ 0 := by
    intro h0
    have h1 : p 1 = 0 := by dsimp [RP] at h0; nlinarith [sq_nonneg (p 2)]
    have h2 : p 2 = 0 := by dsimp [RP] at h0; nlinarith [sq_nonneg (p 1)]
    exact (Complex.slitPlane_ne_zero hpa) (by change phase (p 1) (p 2) = 0; rw [h1,h2]; rfl)
  have hRQ : RQ ≠ 0 := by
    intro h0
    have h1 : q 1 = 0 := by dsimp [RQ] at h0; nlinarith [sq_nonneg (q 2)]
    have h2 : q 2 = 0 := by dsimp [RQ] at h0; nlinarith [sq_nonneg (q 1)]
    exact (Complex.slitPlane_ne_zero hpb) (by change phase (q 1) (q 2) = 0; rw [h1,h2]; rfl)
  have hangP (w) : J w 1 = (p 1*(JP w) 2-p 2*(JP w) 1)/RP := by
    have hd := HasFDerivAt.comp
      (g := fun z : ℝ × ℝ => Complex.arg (phase z.1 z.2))
      (f := fun y : Chart5 => (sourceEndpointA y 1,sourceEndpointA y 2)) x
      (HardSphereB5.SphericalCrofton.Aux.Coarea.phase_fderiv (p 1) (p 2) hpa)
      ((hprojP 1).prodMk (hprojP 2))
    have he : (fun y : Chart5 => Phi y 1) =
        (fun y => Complex.arg (phase (sourceEndpointA y 1) (sourceEndpointA y 2))) := by
      funext y; simp [Phi,pack5,azimuth,EuclideanSpace.single_apply]
    have h := hprojJ 1
    rw [he] at h
    have hm := congrArg (fun L : Chart5 →L[ℝ] ℝ => L w) (h.unique hd)
    change J w 1 = (p 1/RP)*(JP w 2)-(p 2/RP)*(JP w 1) at hm
    convert hm using 1 <;> ring
  have hangQ (w) : J w 3 = (q 1*(JQ w) 2-q 2*(JQ w) 1)/RQ := by
    have hd := HasFDerivAt.comp
      (g := fun z : ℝ × ℝ => Complex.arg (phase z.1 z.2))
      (f := fun y : Chart5 => (sourceEndpointB y 1,sourceEndpointB y 2)) x
      (HardSphereB5.SphericalCrofton.Aux.Coarea.phase_fderiv (q 1) (q 2) hpb)
      ((hprojQ 1).prodMk (hprojQ 2))
    have he : (fun y : Chart5 => Phi y 3) =
        (fun y => Complex.arg (phase (sourceEndpointB y 1) (sourceEndpointB y 2))) := by
      funext y; simp [Phi,pack5,azimuth,EuclideanSpace.single_apply]
    have h := hprojJ 3
    rw [he] at h
    have hm := congrArg (fun L : Chart5 →L[ℝ] ℝ => L w) (h.unique hd)
    change J w 3 = (q 1/RQ)*(JQ w 2)-(q 2/RQ)*(JQ w 1) at hm
    convert hm using 1 <;> ring
  let Ht (Y : Pt) : Pt := (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![1,-Y 0*Y 1/(Y 1^2+Y 2^2),-Y 0*Y 2/(Y 1^2+Y 2^2)]
  let Tt (Y : Pt) : Pt := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,-Y 2,Y 1]
  have hdecomp (Y W : Pt) (ht : inner ℝ Y W = 0) (hR : Y 1^2+Y 2^2 ≠ 0) :
      W = W 0 • Ht Y + ((Y 1*W 2-Y 2*W 1)/(Y 1^2+Y 2^2)) • Tt Y := by
    have hsum : Y 0*W 0+Y 1*W 1+Y 2*W 2 = 0 := by
      simpa [PiLp.inner_apply,Fin.sum_univ_succ,mul_comm,add_assoc] using ht
    ext i
    fin_cases i
    · simp [Ht,Tt]
    · simp [Ht,Tt]
      field_simp [hR]
      linear_combination (Y 1)*hsum
    · simp [Ht,Tt]
      field_simp [hR]
      linear_combination (Y 2)*hsum
  obtain ⟨LP,LQ,hrow⟩ := HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_center_row_split x hreg0 hR
  refine ⟨![LP (Ht p),LP (Tt p),LQ (Ht (q-e)),LQ (Tt (q-e))],?_⟩
  intro w
  have hpdec : JP w = J w 0 • Ht p + J w 1 • Tt p := by
    rw [hheightP,hangP]
    exact hdecomp p (JP w) (htP w) hRP
  have hqdec : JQ w = J w 2 • Ht (q-e) + J w 3 • Tt (q-e) := by
    rw [hheightQ,hangQ]
    have hy1 : (q-e) 1 = q 1 := by change q 1 - 0 = q 1; exact sub_zero _
    have hy2 : (q-e) 2 = q 2 := by change q 2 - 0 = q 2; exact sub_zero _
    have hRqx : (q-e) 1^2 + (q-e) 2^2 ≠ 0 := by rw [hy1,hy2]; exact hRQ
    have h := hdecomp (q-e) (JQ w) (htQ w) hRqx
    rw [hy1,hy2] at h
    exact h
  have h := hrow w
  rw [hpdec,hqdec,map_add,map_add,map_smul,map_smul,map_smul,map_smul] at h
  simpa [J,JP,JQ,mul_comm,add_assoc] using h

