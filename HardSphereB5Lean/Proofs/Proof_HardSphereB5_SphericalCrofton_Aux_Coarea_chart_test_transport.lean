import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_regular_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_Psi_regular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_regular_integral
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_endpoints
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_arg_inverse
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_A
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_B
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_joint_measurable
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 4000

private theorem pack_proj (a b c d f : ℝ) (i : Fin 5) :
    pack5 a b c d f i = ![a,b,c,d,f] i := by
  fin_cases i <;> simp [pack5,PiLp.single_apply]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_chart_test_transport
    (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 → |G D p p'| ≤ C) :
    (∫ x in sourceIncidence, sourceTest G x) = ∫ y in targetIncidence, targetTest G y := by
  let S : Set Chart5 := sourceIncidence ∩ {x | sourceRegular x}
  have hD : Measurable sourceCenter := by unfold sourceCenter; fun_prop
  have hα : Measurable (fun x : Chart5 => x 3) := by fun_prop
  have hβ : Measurable (fun x : Chart5 => x 4) := by fun_prop
  rcases HardSphereB5.SphericalCrofton.Aux.MovingArc.joint_measurable with ⟨hu,hv,hha,hhb⟩
  have hp : Measurable sourceEndpointA := by
    change Measurable (fun x : Chart5 => sourceCenter x+u (sourceCenter x) (x 3))
    apply Measurable.add hD
    change Measurable ((fun z : Pt × ℝ => u z.1 z.2) ∘ (fun x : Chart5 => (sourceCenter x,x 3)))
    exact hu.comp (hD.prodMk hα)
  have hq : Measurable sourceEndpointB := by
    change Measurable (fun x : Chart5 => sourceCenter x+v (sourceCenter x) (x 4))
    apply Measurable.add hD
    change Measurable ((fun z : Pt × ℝ => v z.1 z.2) ∘ (fun x : Chart5 => (sourceCenter x,x 4)))
    exact hv.comp (hD.prodMk hβ)
  have hpc (i : Fin 3) : Measurable (fun x => sourceEndpointA x i) :=
    (show Measurable (fun Y : Pt => Y i) by fun_prop).comp hp
  have hqc (i : Fin 3) : Measurable (fun x => sourceEndpointB x i) :=
    (show Measurable (fun Y : Pt => Y i) by fun_prop).comp hq
  have hunit : Measurable unitDir := by
    change Measurable (fun D : Pt => ‖D‖⁻¹ • D)
    exact measurable_id.norm.inv.smul measurable_id
  have hf0 : Measurable centerFrame0 := by
    change Measurable (unitDir ∘ (fun D : Pt => e-(inner ℝ (unitDir D) e) • unitDir D))
    exact hunit.comp (measurable_const.sub ((hunit.inner (𝕜 := ℝ) (g := fun _ : Pt => e) measurable_const).smul hunit))
  have hcross (f g : Pt → Pt) (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun D => cross (f D) (g D)) := by
    unfold cross
    apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
    apply measurable_pi_lambda
    have h1 (i : Fin 3) : Measurable (fun D => f D i) :=
      (show Measurable (fun Y : Pt => Y i) by fun_prop).comp hf
    have h2 (i : Fin 3) : Measurable (fun D => g D i) :=
      (show Measurable (fun Y : Pt => Y i) by fun_prop).comp hg
    intro i
    fin_cases i
    · change Measurable (fun D => f D 1*g D 2-f D 2*g D 1)
      exact ((h1 1).mul (h2 2)).sub ((h1 2).mul (h2 1))
    · change Measurable (fun D => f D 2*g D 0-f D 0*g D 2)
      exact ((h1 2).mul (h2 0)).sub ((h1 0).mul (h2 2))
    · change Measurable (fun D => f D 0*g D 1-f D 1*g D 0)
      exact ((h1 0).mul (h2 1)).sub ((h1 1).mul (h2 0))
  have hf1 : Measurable centerFrame1 := hcross unitDir centerFrame0 hunit hf0
  have hphase (f g : Chart5 → ℝ) (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun x => phase (f x) (g x)) := by
    have hrepr (a b : ℝ) : phase a b = (a : ℂ)+(b : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [phase]
    simp_rw [hrepr]
    exact (Complex.measurable_ofReal.comp hf).add ((Complex.measurable_ofReal.comp hg).mul measurable_const)
  have hpPhase : Measurable (fun x => phase (sourceEndpointA x 1) (sourceEndpointA x 2)) :=
    hphase _ _ (hpc 1) (hpc 2)
  have hqPhase : Measurable (fun x => phase (sourceEndpointB x 1) (sourceEndpointB x 2)) :=
    hphase _ _ (hqc 1) (hqc 2)
  have hsep : Measurable (fun x => sourceEndpointB x-sourceEndpointA x) := hq.sub hp
  have hdisp : Measurable (fun x => sourceCenter x-midpoint ℝ (sourceEndpointA x) (sourceEndpointB x)) := by
    simp only [midpoint_eq_smul_add]
    fun_prop
  have hcenterPhase : Measurable (fun x => centerPhase (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x)) :=
    hphase _ _ ((hf0.comp hsep).inner (𝕜 := ℝ) hdisp) ((hf1.comp hsep).inner (𝕜 := ℝ) hdisp)
  let E : Set Chart5 := {x | x 3 ∈ Set.Ioo (-Real.pi) Real.pi ∧
    x 4 ∈ Set.Ioo (-Real.pi) Real.pi ∧ |sourceEndpointA x 0| < 1 ∧
    |sourceEndpointB x 0-1| < 1 ∧ centerFrame0 (sourceEndpointB x-sourceEndpointA x) ≠ 0 ∧
    phase (sourceEndpointA x 1) (sourceEndpointA x 2) ∈ Complex.slitPlane ∧
    phase (sourceEndpointB x 1) (sourceEndpointB x 2) ∈ Complex.slitPlane ∧
    centerPhase (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) ∈ Complex.slitPlane}
  have hEm : MeasurableSet E :=
    ((measurableSet_Ioo.preimage hα).inter
      ((measurableSet_Ioo.preimage hβ).inter
        ((measurableSet_lt (hpc 0).abs measurable_const).inter
          ((measurableSet_lt ((hqc 0).sub measurable_const).abs measurable_const).inter
            (((measurableSet_singleton (0 : Pt)).preimage (hf0.comp hsep)).compl.inter
              ((Complex.isOpen_slitPlane.measurableSet.preimage hpPhase).inter
                ((Complex.isOpen_slitPlane.measurableSet.preimage hqPhase).inter
                  (Complex.isOpen_slitPlane.measurableSet.preimage hcenterPhase))))))))
  have hSform : S = sourceIncidence ∩ E := by
    ext x
    simp only [S,E,Set.mem_inter_iff,Set.mem_setOf_eq,sourceIncidence,sourceRegular]
    tauto
  have hSm : MeasurableSet S := by
    rw [hSform]
    exact HardSphereB5.SphericalCrofton.Aux.Coarea.sourceIncidence_measurable.inter hEm
  have hS : ∀ x ∈ S, sourceRegular x ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)) := by
    intro x hx
    rcases hx.1 with ⟨hoff,hL,hR,hAi,hBi,hFA,hFB,hz0,hz1⟩
    exact ⟨hx.2,hR,hAi,hBi⟩
  have hreconstruct (x : Chart5) (hx : x ∈ S) :
      targetEndpointA (Phi x) = sourceEndpointA x ∧
      targetEndpointB (Phi x) = sourceEndpointB x ∧
      targetCenter (Phi x) = sourceCenter x := by
    rcases hx.2 with ⟨hoff,hL,hFA,hFB,hz0,hz1,hθ,hψ,hp0,hq0,hf,hpa,hpb,hpc⟩
    have hnA : ‖sourceCenter x‖ ≤ 1 := by
      simpa [LamC,Metric.mem_closedBall,dist_zero_right] using hL.1
    have hnB : ‖sourceCenter x-e‖ ≤ 1 := by
      simpa [LamC,Metric.mem_closedBall,dist_eq_norm] using hL.2
    have hnormA := HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A (sourceCenter x) hoff (by linarith) (x 3)
    have hnormB := HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_B (sourceCenter x) hoff (by linarith) (x 4)
    have hcontactA : dist (sourceCenter x) (sourceEndpointA x) = 1 := by
      change dist (sourceCenter x) (sourceCenter x+u (sourceCenter x) (x 3)) = 1
      rw [dist_eq_norm,show sourceCenter x-(sourceCenter x+u (sourceCenter x) (x 3)) = -u (sourceCenter x) (x 3) by abel,
        norm_neg,hnormA.1]
    have hcontactB : dist (sourceCenter x) (sourceEndpointB x) = 1 := by
      change dist (sourceCenter x) (sourceCenter x+v (sourceCenter x) (x 4)) = 1
      rw [dist_eq_norm,show sourceCenter x-(sourceCenter x+v (sourceCenter x) (x 4)) = -v (sourceCenter x) (x 4) by abel,
        norm_neg,hnormB.1]
    have hend := HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_endpoints x hFA hFB hp0 hq0
    refine ⟨hend.1,hend.2,?_⟩
    unfold targetCenter
    rw [hend.1,hend.2]
    have hpsi : (Phi x) 4 = Complex.arg (centerPhase (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x)) := by
      simp [Phi,pack_proj]
    rw [hpsi]
    exact HardSphereB5.SphericalCrofton.Aux.Coarea.center_arg_inverse _ _ _ hz0 (by linarith) hcontactA hcontactB hf
  have himage : Phi '' S ⊆ targetIncidence := by
    rintro y ⟨x,hx,rfl⟩
    have he := hreconstruct x hx
    rcases hx.2 with ⟨hoff,hL,hFA,hFB,hz0,hz1,hθ,hψ,hp0,hq0,hf,hpa,hpb,hpc⟩
    have he_norm : ‖e‖ = 1 := by simp [e,EuclideanSpace.norm_eq]
    have hpnorm : ‖sourceEndpointA x‖ = 1 := by
      simpa [FA,Metric.mem_sphere,dist_zero_right] using hFA.1
    have hpdist : ‖sourceEndpointA x-e‖ ≤ 1 := by
      simpa [FA,Metric.mem_closedBall,dist_eq_norm] using hFA.2
    have hqnorm : ‖sourceEndpointB x-e‖ = 1 := by
      simpa [FB,Metric.mem_sphere,dist_eq_norm] using hFB.1
    have hqdist : ‖sourceEndpointB x‖ ≤ 1 := by
      simpa [FB,Metric.mem_closedBall,dist_zero_right] using hFB.2
    have hpinner : inner ℝ (sourceEndpointA x) e = sourceEndpointA x 0 := by
      simp [e,PiLp.inner_apply,Fin.sum_univ_succ]
    have hqinner : inner ℝ (sourceEndpointB x-e) e = sourceEndpointB x 0-1 := by
      simp [e,PiLp.inner_apply,Fin.sum_univ_succ]
    have hpheight : (1/2 : ℝ) ≤ sourceEndpointA x 0 := by
      have h := norm_sub_sq_real (sourceEndpointA x) e
      rw [hpnorm,he_norm,hpinner] at h
      nlinarith [norm_nonneg (sourceEndpointA x-e)]
    have hqheight : sourceEndpointB x 0-1 ≤ (-1/2 : ℝ) := by
      have h := norm_add_sq_real (sourceEndpointB x-e) e
      rw [sub_add_cancel,hqnorm,he_norm,hqinner] at h
      nlinarith [norm_nonneg (sourceEndpointB x)]
    change (Phi x) 0 ∈ Set.Icc (1/2 : ℝ) 1 ∧ (Phi x) 2 ∈ Set.Icc (-1 : ℝ) (-1/2) ∧
      (Phi x) 1 ∈ Set.Icc (-Real.pi) Real.pi ∧ (Phi x) 3 ∈ Set.Icc (-Real.pi) Real.pi ∧
      (Phi x) 4 ∈ Set.Icc (-Real.pi) Real.pi ∧
      0 < dist (targetEndpointA (Phi x)) (targetEndpointB (Phi x)) ∧
      dist (targetEndpointA (Phi x)) (targetEndpointB (Phi x)) < 1 ∧ targetCenter (Phi x) ∈ LamC
    rw [he.1,he.2.1,he.2.2]
    simp only [Phi,pack_proj,Matrix.cons_val_zero,Matrix.cons_val_succ]
    refine ⟨⟨hpheight,(abs_lt.mp hp0).2.le⟩,⟨(abs_lt.mp hq0).1.le,hqheight⟩,?_,?_,?_,hz0,hz1,hL⟩
    · exact ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩
    · exact ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩
    · exact ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩
  have hsourceAE : sourceIncidence =ᵐ[volume] S := by
    filter_upwards [HardSphereB5.SphericalCrofton.Aux.Coarea.source_regular_ae] with x hx
    apply propext
    constructor
    · intro hi
      exact ⟨hi,hx hi⟩
    · exact fun hi => hi.1
  have htargetAE : Phi '' S =ᵐ[volume] targetIncidence := by
    filter_upwards [HardSphereB5.SphericalCrofton.Aux.Coarea.target_regular_ae] with y hy
    apply propext
    constructor
    · exact fun him => himage him
    · intro ht
      have h := HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_Psi_regular y (hy ht)
      refine ⟨Psi y,?_,h.1⟩
      refine ⟨?_,h.2.1⟩
      rcases h.2.1 with ⟨hoff,hL,hFA,hFB,hz0,hz1,hθ,hψ,hp0,hq0,hf,hpa,hpb,hpc⟩
      exact ⟨hoff,hL,h.2.2.1,h.2.2.2.1,h.2.2.2.2,hFA,hFB,hz0,hz1⟩
  have htest (x : Chart5) (hx : x ∈ S) :
      (dist (sourceEndpointA x) (sourceEndpointB x)/
        (‖sourceCenter x‖*‖sourceCenter x-e‖))*targetTest G (Phi x) = sourceTest G x := by
    have he := hreconstruct x hx
    have hoff := hx.2.1
    have hD0 : sourceCenter x ≠ 0 := by
      intro hz; exact hoff 0 (by simpa using hz)
    have hDe : sourceCenter x ≠ e := by
      intro he; exact hoff 1 (by simpa using he)
    have hz0 : 0 < dist (sourceEndpointA x) (sourceEndpointB x) := hx.2.2.2.2.2.1
    unfold targetTest sourceTest
    rw [he.1,he.2.1,he.2.2]
    field_simp [ne_of_gt hz0,norm_ne_zero_iff.mpr hD0,norm_ne_zero_iff.mpr (sub_ne_zero.mpr hDe)]
  calc
    (∫ x in sourceIncidence,sourceTest G x) = ∫ x in S,sourceTest G x := setIntegral_congr_set hsourceAE
    _ = ∫ x in S,(dist (sourceEndpointA x) (sourceEndpointB x)/
        (‖sourceCenter x‖*‖sourceCenter x-e‖))*targetTest G (Phi x) := by
      apply setIntegral_congr_fun hSm
      intro x hx
      exact (htest x hx).symm
    _ = ∫ y in Phi '' S,targetTest G y :=
      (HardSphereB5.SphericalCrofton.Aux.Coarea.Phi_regular_integral S hS hSm (targetTest G)).symm
    _ = ∫ y in targetIncidence,targetTest G y := setIntegral_congr_set htargetAE
