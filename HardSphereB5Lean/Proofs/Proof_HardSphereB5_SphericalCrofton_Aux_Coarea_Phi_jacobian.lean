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
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_oriented_deriv_A
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_cylinder_contact_covector
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_density_det5
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_center_row_elimination
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
set_option maxHeartbeats 1800000

noncomputable section
private theorem cross_neg_native (a b : Pt) : cross (-a) (-b) = cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring
private theorem reflect_axis (D : Pt) : nAv (e-D)= -nBv D := by
  simp only [nAv, nBv, norm_sub_rev e D, smul_neg]

private theorem reflect_raw (D : Pt) : rawA (e-D)= -rawB D := by
  rw [rawA, reflect_axis, rawB]
  simp only [inner_neg_left, inner_neg_right, neg_smul, smul_neg]
  module

private theorem reflect_unit (D : Pt) : unitDir (rawA (e-D))= -unitDir (rawB D) := by
  rw [reflect_raw]
  simp [unitDir]

private theorem reflect_E0 (D : Pt) : EA (e-D) 0= -(EB D 0) := by
  simpa only [EA, EB, Matrix.cons_val_zero] using reflect_unit D

private theorem reflect_E1 (D : Pt) : EA (e-D) 1= -(EB D 1) := by
  change cross (nAv (e-D)) (unitDir (rawA (e-D)))=
    -(-cross (nBv D) (unitDir (rawB D)))
  rw [reflect_axis, reflect_unit, cross_neg_native, neg_neg]

private theorem reflect_center (D : Pt) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.cA (e-D)= -HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, HardSphereB5.SphericalCrofton.Aux.MovingArc.cB]
  module

private theorem reflect_radius (D : Pt) : rA (e-D)=rB D := by
  simp only [rA, rB, norm_sub_rev e D]

private theorem reflect_chart (D : Pt) (t : ℝ) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t= -HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, HardSphereB5.SphericalCrofton.Aux.MovingArc.v,
    circlePt, reflect_center, reflect_E0, reflect_E1, reflect_radius]
  module

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_jacobian (x : Chart5)
    (hreg : sourceRegular x)
    (hR : Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1)
    (hα : x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)))
    (hβ : x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x))) :
    |LinearMap.det (fderiv ℝ Phi x).toLinearMap| =
      dist (sourceEndpointA x) (sourceEndpointB x) /
        (‖sourceCenter x‖ * ‖sourceCenter x-e‖) := by
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
  let D : Pt := sourceCenter x
  let uc : Pt := p-D
  let vc : Pt := q-D
  let JD := fderiv ℝ sourceCenter x
  let S (i : Fin 5) : Chart5 := EuclideanSpace.single i 1
  let DS : Chart5 →L[ℝ] Pt :=
    ((@EuclideanSpace.proj (Fin 5) ℝ _ 0).smulRight e) +
    ((@EuclideanSpace.proj (Fin 5) ℝ _ 1).smulRight e1) +
    ((@EuclideanSpace.proj (Fin 5) ℝ _ 2).smulRight e2)
  have hDS : HasFDerivAt sourceCenter DS x := by
    change HasFDerivAt DS DS x
    exact DS.hasFDerivAt
  have hJD : JD = DS := hDS.fderiv
  have hDapply (w : Chart5) : JD w = w 0 • e+w 1 • e1+w 2 • e2 := by
    rw [hJD]
    rfl
  have hunitU : ∀ᶠ y in nhds x, ‖sourceEndpointA y-sourceCenter y‖ = 1 := by
    filter_upwards [hoff_near,hnearA] with y hy hr
    simpa [sourceEndpointA] using
      (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A (sourceCenter y) hy hr (y 3)).1
  have hunitV : ∀ᶠ y in nhds x, ‖sourceEndpointB y-sourceCenter y‖ = 1 := by
    filter_upwards [hoff_near,hnearB] with y hy hr
    simpa [sourceEndpointB] using
      (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_B (sourceCenter y) hy hr (y 4)).1
  have htU : ∀ w, inner ℝ uc ((JP-JD) w) = 0 :=
    htangent (fun y => sourceEndpointA y-sourceCenter y) (JP-JD)
      ((hP.differentiableAt (by simp)).hasFDerivAt.sub
        (hDsm.differentiableAt (by simp)).hasFDerivAt) hunitU
  have htV : ∀ w, inner ℝ vc ((JQ-JD) w) = 0 :=
    htangent (fun y => sourceEndpointB y-sourceCenter y) (JQ-JD)
      ((hQ.differentiableAt (by simp)).hasFDerivAt.sub
        (hDsm.differentiableAt (by simp)).hasFDerivAt) hunitV
  have hcU (w) : inner ℝ uc (JP w) = inner ℝ uc (JD w) := by
    have h := htU w
    simpa only [ContinuousLinearMap.sub_apply,inner_sub_right,sub_eq_zero] using h
  have hcV (w) : inner ℝ vc (JQ w) = inner ℝ vc (JD w) := by
    have h := htV w
    simpa only [ContinuousLinearMap.sub_apply,inner_sub_right,sub_eq_zero] using h
  have hcurve (j : Fin 5) : HasDerivAt (fun t : ℝ => x+t • S j) (S j) 0 := by
    let Lj : ℝ →L[ℝ] Chart5 := (ContinuousLinearMap.id ℝ ℝ).smulRight (S j)
    have hj : HasDerivAt Lj (Lj 1) 0 := Lj.hasDerivAt
    have h := hj.const_add x
    simpa only [Lj,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
      one_smul] using h
  have hPline (j : Fin 5) : HasDerivAt (fun t : ℝ => sourceEndpointA (x+t • S j)) (JP (S j)) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt_of_eq
      (l := sourceEndpointA) (f := fun t : ℝ => x+t • S j) (f' := S j)
      (l' := JP) (y := x) (0 : ℝ)
      (hP.differentiableAt (by simp)).hasFDerivAt (hcurve j) (by simp)
    exact h
  have hQline (j : Fin 5) : HasDerivAt (fun t : ℝ => sourceEndpointB (x+t • S j)) (JQ (S j)) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt_of_eq
      (l := sourceEndpointB) (f := fun t : ℝ => x+t • S j) (f' := S j)
      (l' := JQ) (y := x) (0 : ℝ)
      (hQ.differentiableAt (by simp)).hasFDerivAt (hcurve j) (by simp)
    exact h
  have hAfun : (fun t : ℝ => sourceEndpointA (x+t • S 3)) =
      (fun t => D+HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3+t)) := by
    funext t
    simp [D,sourceEndpointA,sourceCenter,S,EuclideanSpace.single_apply]
  have hAconst : (fun t : ℝ => sourceEndpointA (x+t • S 4)) = (fun _ => p) := by
    funext t
    simp [p,sourceEndpointA,sourceCenter,S,EuclideanSpace.single_apply]
  have hBfun : (fun t : ℝ => sourceEndpointB (x+t • S 4)) =
      (fun t => D+HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4+t)) := by
    funext t
    simp [D,sourceEndpointB,sourceCenter,S,EuclideanSpace.single_apply]
  have hBconst : (fun t : ℝ => sourceEndpointB (x+t • S 3)) = (fun _ => q) := by
    funext t
    simp [q,sourceEndpointB,sourceCenter,S,EuclideanSpace.single_apply]
  have ha : JP (S 3) = cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3)) := by
    have ht : HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D)
        (cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3))) (x 3+0) := by
      simpa only [add_zero] using HardSphereB5.SphericalCrofton.Aux.MovingArc.oriented_deriv_A D hoff (x 3)
    have hs := HasDerivAt.scomp (g₁ := HardSphereB5.SphericalCrofton.Aux.MovingArc.u D)
      (h := fun t : ℝ => x 3+t) (0 : ℝ) ht ((hasDerivAt_id (0 : ℝ)).const_add (x 3))
    have hs' : HasDerivAt (fun t : ℝ => D+HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3+t))
        (cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3))) 0 := by
      simpa only [Function.comp_apply, one_smul] using hs.const_add D
    have h := hPline 3
    rw [hAfun] at h
    exact h.unique hs'
  have ha0 : JP (S 4) = 0 := by
    have h := hPline 4
    rw [hAconst] at h
    exact h.unique (hasDerivAt_const (0 : ℝ) p)
  have hb0 : JQ (S 3) = 0 := by
    have h := hQline 3
    rw [hBconst] at h
    exact h.unique (hasDerivAt_const (0 : ℝ) q)
  have href : offAxis (e-D) := by
    intro t ht
    apply hoff (1-t)
    calc
      D = e-(e-D) := by abel
      _ = e-t • e := by rw [ht]
      _ = (1-t) • e := by module
  have hb : JQ (S 4) = -cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4)) := by
    have hv : HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D)
        (-cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4))) (x 4) := by
      have h := (HardSphereB5.SphericalCrofton.Aux.MovingArc.oriented_deriv_A (e-D) href (x 4)).neg
      simp_rw [reflect_chart] at h
      rw [reflect_axis] at h
      have hcross : cross (-nBv D) (-HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4)) =
          cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4)) := cross_neg_native _ _
      rw [hcross] at h
      have he : -HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) =
          HardSphereB5.SphericalCrofton.Aux.MovingArc.v D := by
        funext t
        rw [Pi.neg_apply, reflect_chart, neg_neg]
      rw [he] at h
      exact h
    have ht : HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D)
        (-cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4))) (x 4+0) := by
      simpa only [add_zero] using hv
    have hs := HasDerivAt.scomp (g₁ := HardSphereB5.SphericalCrofton.Aux.MovingArc.v D)
      (h := fun t : ℝ => x 4+t) (0 : ℝ) ht ((hasDerivAt_id (0 : ℝ)).const_add (x 4))
    have hs' : HasDerivAt (fun t : ℝ => D+HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4+t))
        (-cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4))) 0 := by
      simpa only [Function.comp_apply, one_smul] using hs.const_add D
    have h := hQline 4
    rw [hBfun] at h
    exact h.unique hs'
  have hsmul_cross (a : ℝ) (U V : Pt) : cross (a • U) V = a • cross U V := by
    ext i; fin_cases i <;> simp [SphereGeom.cross,cross_apply] <;> ring
  have hgeomA : cross D (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3)) = cross p uc := by
    ext i; fin_cases i <;> simp [p,uc,D,sourceEndpointA,SphereGeom.cross,cross_apply] <;> ring
  have hgeomB : cross (e-D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (x 4)) = -cross (q-e) vc := by
    ext i; fin_cases i <;> simp [q,vc,D,sourceEndpointB,SphereGeom.cross,cross_apply] <;> ring
  have hcolA : JP (S 3) = -(‖D‖)⁻¹ • cross p uc := by
    rw [ha,nAv,hsmul_cross]
    have hn : cross (-D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3)) =
        -cross D (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (x 3)) := by
      ext i; fin_cases i <;> simp [SphereGeom.cross,cross_apply] <;> ring
    rw [hn,hgeomA]
    simp
  have hcolB : JQ (S 4) = (‖D-e‖)⁻¹ • cross (q-e) vc := by
    rw [hb,nBv,hsmul_cross,hgeomB]
    simp
  obtain ⟨k,hcenter⟩ := HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_center_row_elimination x hreg0 hR
  let a : ℝ := ‖D‖
  let b : ℝ := ‖D-e‖
  let z : ℝ := dist p q
  let rr : ℝ := Real.sqrt (1-z^2/4)
  have ha_pos : 0 < a := norm_pos_iff.mpr hD
  have hb_pos : 0 < b := norm_pos_iff.mpr (sub_ne_zero.mpr hDe)
  have hz_pos : 0 < z := hz0
  have hrad_pos : 0 < 1-z^2/4 := by dsimp [z,p,q]; nlinarith
  have hrr_pos : 0 < rr := Real.sqrt_pos.mpr hrad_pos
  have hrr_sq : rr^2 = 1-z^2/4 := Real.sq_sqrt (le_of_lt hrad_pos)
  have hu : ‖uc‖ = 1 := by
    simpa [uc,p,D,sourceEndpointA] using
      (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A D hoff (by change ‖sourceCenter x‖ < 2; linarith) (x 3)).1
  have hv : ‖vc‖ = 1 := by
    simpa [vc,q,D,sourceEndpointB] using
      (HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_B D hoff (by change ‖sourceCenter x-e‖ < 2; linarith) (x 4)).1
  have huv : ‖uc-vc‖ = z := by
    dsimp [uc,vc,z]
    rw [sub_sub_sub_cancel_right,←dist_eq_norm]
  let α₀ : ℝ := uc 0-p 0*(p 1*uc 1+p 2*uc 2)/RP
  let α₁ : ℝ := p 1*uc 2-p 2*uc 1
  let β₀ : ℝ := vc 0-(q 0-1)*(q 1*vc 1+q 2*vc 2)/RQ
  let β₁ : ℝ := q 1*vc 2-q 2*vc 1
  have hcP (w) : α₀ * J w 0 + α₁ * J w 1 = inner ℝ uc (JD w) := by
    rw [hheightP,hangP]
    have h := (HardSphereB5.SphericalCrofton.Aux.Coarea.cylinder_contact_covector p uc (JP w) (htP w) hRP).1
    change α₀ * JP w 0+α₁*((p 1*JP w 2-p 2*JP w 1)/RP)=inner ℝ uc (JP w) at h
    rw [hcU] at h
    exact h
  have hcQ (w) : β₀ * J w 2 + β₁ * J w 3 = inner ℝ vc (JD w) := by
    rw [hheightQ,hangQ]
    have hy1 : (q-e) 1 = q 1 := by change q 1 - 0 = q 1; exact sub_zero _
    have hy2 : (q-e) 2 = q 2 := by change q 2 - 0 = q 2; exact sub_zero _
    have hRq : (q-e) 1^2+(q-e) 2^2 ≠ 0 := by rw [hy1,hy2]; exact hRQ
    have h := (HardSphereB5.SphericalCrofton.Aux.Coarea.cylinder_contact_covector (q-e) vc (JQ w) (htQ w) hRq).1
    rw [hy1,hy2] at h
    change β₀ * JQ w 0+β₁*((q 1*JQ w 2-q 2*JQ w 1)/RQ)=inner ℝ vc (JQ w) at h
    rw [hcV] at h
    exact h
  have hAcols : J (S 3) 0 = -α₁/a ∧ J (S 3) 1 = α₀/a := by
    have hct := HardSphereB5.SphericalCrofton.Aux.Coarea.cylinder_contact_covector p uc (JP (S 3)) (htP (S 3)) hRP
    have hc0 : (cross p uc) 0 = α₁ := hct.2.1
    have hc1 : (p 1*(cross p uc) 2-p 2*(cross p uc) 1)/RP = -α₀ := hct.2.2
    constructor
    · rw [hheightP,hcolA]
      change -(a)⁻¹*(cross p uc) 0 = -α₁/a
      rw [hc0]
      ring
    · rw [hangP,hcolA]
      change (p 1*(-(a)⁻¹*(cross p uc) 2)-p 2*(-(a)⁻¹*(cross p uc) 1))/RP = α₀/a
      calc
        _ = -(a)⁻¹*((p 1*(cross p uc) 2-p 2*(cross p uc) 1)/RP) := by ring
        _ = α₀/a := by rw [hc1]; ring
  have hBcols : J (S 4) 2 = β₁/b ∧ J (S 4) 3 = -β₀/b := by
    have hy1 : (q-e) 1 = q 1 := by change q 1-0=q 1; exact sub_zero _
    have hy2 : (q-e) 2 = q 2 := by change q 2-0=q 2; exact sub_zero _
    have hRq : (q-e) 1^2+(q-e) 2^2 ≠ 0 := by rw [hy1,hy2]; exact hRQ
    have hct := HardSphereB5.SphericalCrofton.Aux.Coarea.cylinder_contact_covector (q-e) vc (JQ (S 4)) (htQ (S 4)) hRq
    have hc0 : (cross (q-e) vc) 0 = β₁ := by
      have h := hct.2.1
      rw [hy1,hy2] at h
      exact h
    have hc1 : (q 1*(cross (q-e) vc) 2-q 2*(cross (q-e) vc) 1)/RQ = -β₀ := by
      have hy0 : (q-e) 0 = q 0-1 := by rfl
      have h := hct.2.2
      rw [hy0,hy1,hy2] at h
      exact h
    constructor
    · rw [hheightQ,hcolB]
      change b⁻¹*(cross (q-e) vc) 0 = β₁/b
      rw [hc0]
      ring
    · rw [hangQ,hcolB]
      change (q 1*(b⁻¹*(cross (q-e) vc) 2)-q 2*(b⁻¹*(cross (q-e) vc) 1))/RQ = -β₀/b
      calc
        _ = b⁻¹*((q 1*(cross (q-e) vc) 2-q 2*(cross (q-e) vc) 1)/RQ) := by ring
        _ = -β₀/b := by rw [hc1]; ring
  have hAzeros : J (S 4) 0 = 0 ∧ J (S 4) 1 = 0 := by
    constructor
    · rw [hheightP,ha0]; rfl
    · rw [hangP,ha0]; simp
  have hBzeros : J (S 3) 2 = 0 ∧ J (S 3) 3 = 0 := by
    constructor
    · rw [hheightQ,hb0]; rfl
    · rw [hangQ,hb0]; simp
  let M : Matrix (Fin 5) (Fin 5) ℝ := fun i j => J (S j) i
  let A₀ : Fin 3 → ℝ := ![M 0 0,M 0 1,M 0 2]
  let A₁ : Fin 3 → ℝ := ![M 1 0,M 1 1,M 1 2]
  let B₀ : Fin 3 → ℝ := ![M 2 0,M 2 1,M 2 2]
  let B₁ : Fin 3 → ℝ := ![M 3 0,M 3 1,M 3 2]
  let c : Fin 3 → ℝ := fun i => (cross uc vc) i/(z*rr^2)
  have hCA : α₀ • A₀+α₁ • A₁ = fun i => uc i := by
    ext i
    fin_cases i
    · have h := hcP (S 0)
      rw [hDapply] at h
      simpa [A₀,A₁,M,S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ] using h
    · have h := hcP (S 1)
      rw [hDapply] at h
      simpa [A₀,A₁,M,S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ] using h
    · have h := hcP (S 2)
      rw [hDapply] at h
      simpa [A₀,A₁,M,S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ] using h
  have hCB : β₀ • B₀+β₁ • B₁ = fun i => vc i := by
    ext i
    fin_cases i
    · have h := hcQ (S 0)
      rw [hDapply] at h
      simpa [B₀,B₁,M,S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ] using h
    · have h := hcQ (S 1)
      rw [hDapply] at h
      simpa [B₀,B₁,M,S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ] using h
    · have h := hcQ (S 2)
      rw [hDapply] at h
      simpa [B₀,B₁,M,S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ] using h
  let ks : Fin 5 → ℝ := ![-k 0,-k 1,-k 2,-k 3,1]
  let MR : Matrix (Fin 5) (Fin 5) ℝ := M.updateRow 4 (∑ i,ks i • M i)
  have hdetMR : MR.det = M.det := by
    simpa [MR,ks] using Matrix.det_updateRow_sum M 4 ks
  have hlast (j : Fin 5) : MR 4 j =
      (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S j)) := by
    have h := hcenter (S j)
    change J (S j) 4 = (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S j)) +
      k 0*J (S j) 0+k 1*J (S j) 1+k 2*J (S j) 2+k 3*J (S j) 3 at h
    change (∑ i : Fin 5,ks i • M i) j = _
    simp only [Fin.sum_univ_succ,ks,M,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Pi.smul_apply,Pi.add_apply,smul_eq_mul,one_mul,Fintype.sum_empty,Pi.zero_apply,add_zero]
    change -k 0*J (S j) 0 + (-k 1*J (S j) 1 +
      (-k 2*J (S j) 2 + (-k 3*J (S j) 3 + J (S j) 4))) =
      (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S j))
    rw [h]
    ring
  let MP : Matrix (Fin 5) (Fin 5) ℝ :=
    ![![A₀ 0,A₀ 1,A₀ 2,-α₁/a,0],
      ![A₁ 0,A₁ 1,A₁ 2,α₀/a,0],
      ![B₀ 0,B₀ 1,B₀ 2,0,β₁/b],
      ![B₁ 0,B₁ 1,B₁ 2,0,-β₀/b],
      ![c 0,c 1,c 2,0,0]]
  have hMRP : MR = MP := by
    ext i j
    fin_cases i
    · fin_cases j <;> simp [MR,MP,Matrix.updateRow,M,A₀,A₁,B₀,B₁,hAcols.1,hAzeros.1]
    · fin_cases j <;> simp [MR,MP,Matrix.updateRow,M,A₀,A₁,B₀,B₁,hAcols.2,hAzeros.2]
    · fin_cases j <;> simp [MR,MP,Matrix.updateRow,M,A₀,A₁,B₀,B₁,hBcols.1,hBzeros.1]
    · fin_cases j <;> simp [MR,MP,Matrix.updateRow,M,A₀,A₁,B₀,B₁,hBcols.2,hBzeros.2]
    · change MR 4 j = MP 4 j
      rw [hlast]
      fin_cases j
      · change (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S 0)) = (cross uc vc) 0/(z*rr^2)
        rw [hDapply,hrr_sq]
        simp only [div_eq_mul_inv,mul_inv_rev]
        simp [S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ]
        all_goals ring
      · change (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S 1)) = (cross uc vc) 1/(z*rr^2)
        rw [hDapply,hrr_sq]
        simp only [div_eq_mul_inv,mul_inv_rev]
        simp [S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ]
        all_goals ring
      · change (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S 2)) = (cross uc vc) 2/(z*rr^2)
        rw [hDapply,hrr_sq]
        simp only [div_eq_mul_inv,mul_inv_rev]
        simp [S,e,e1,e2,EuclideanSpace.single_apply,PiLp.inner_apply,Fin.sum_univ_succ]
        all_goals ring
      · change (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S 3)) = 0
        rw [hDapply]
        simp [S,EuclideanSpace.single_apply]
      · change (z*(1-z^2/4))⁻¹*inner ℝ (cross uc vc) (JD (S 4)) = 0
        rw [hDapply]
        simp [S,EuclideanSpace.single_apply]
  have hphysical : |MP.det| = z/(a*b) :=
    HardSphereB5.SphericalCrofton.Aux.Coarea.incidence_density_det5 A₀ A₁ B₀ B₁ uc vc
      α₀ α₁ β₀ β₁ a b z rr ha_pos hb_pos hz_pos hrr_pos hCA hCB hu hv huv hrr_sq
  let bs := (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
  have hMrepr : LinearMap.toMatrix bs bs J.toLinearMap = M := by
    ext i j
    simp [LinearMap.toMatrix_apply,bs,EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr,S,M]
  have hdetM : M.det = LinearMap.det J.toLinearMap := by
    rw [←hMrepr]
    exact LinearMap.det_toMatrix bs J.toLinearMap
  change |LinearMap.det J.toLinearMap| = z/(a*b)
  rw [←hdetM,←hdetMR,hMRP]
  exact hphysical
