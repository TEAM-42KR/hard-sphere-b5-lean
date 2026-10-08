import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_density_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_coordinates_preserving
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_joint_measurable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
set_option maxHeartbeats 1000000
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_test_integrable (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ q ∈ FB,
      dist D p = 1 → dist D q = 1 → 0 < dist p q → dist p q < 1 → |G D p q| ≤ C)
    (S : Set Chart5) (hSm : MeasurableSet S)
    (hS : ∀ x ∈ S, sourceCenter x ∈ LamC ∧
      x 3 ∈ Set.Icc (-Real.pi) Real.pi ∧ x 4 ∈ Set.Icc (-Real.pi) Real.pi ∧
      sourceEndpointA x ∈ FA ∧ sourceEndpointB x ∈ FB ∧
      dist (sourceCenter x) (sourceEndpointA x) = 1 ∧
      dist (sourceCenter x) (sourceEndpointB x) = 1 ∧
      0 < dist (sourceEndpointA x) (sourceEndpointB x) ∧
      dist (sourceEndpointA x) (sourceEndpointB x) < 1) :
    IntegrableOn (fun x => G (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) /
      (‖sourceCenter x‖ * ‖sourceCenter x-e‖)) S volume  := by
  let I : Set ℝ := Set.Icc (-Real.pi) Real.pi
  let bD : Pt → ℝ := LamC.indicator (fun D => (‖D‖ * ‖D-e‖)⁻¹)
  let bθ : ℝ → ℝ := I.indicator (fun _ => 1)
  let H : Pt × ℝ × ℝ → ℝ := fun q => C * (bD q.1 * (bθ q.2.1 * bθ q.2.2))
  have hL : MeasurableSet LamC := (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).measurableSet
  have hd : Integrable bD := (integrable_indicator_iff hL).mpr
    HardSphereB5.SphericalCrofton.Aux.Coarea.center_density_integrable
  have hθ : Integrable bθ := (integrable_indicator_iff measurableSet_Icc).mpr
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn.integrableOn_compact isCompact_Icc)
  have hH : Integrable H := (hd.mul_prod (hθ.mul_prod hθ)).const_mul C
  have hmap := HardSphereB5.SphericalCrofton.Aux.Coarea.source_coordinates_preserving
  have hdom : Integrable (fun x : Chart5 => H (sourceCenter x,x 3,x 4)) :=
    hmap.integrable_comp_of_integrable hH
  rcases HardSphereB5.SphericalCrofton.Aux.MovingArc.joint_measurable with ⟨hu,hv,hhalfA,hhalfB⟩
  have hD : Measurable sourceCenter := by unfold sourceCenter; fun_prop
  have hα : Measurable (fun x : Chart5 => x 3) := by fun_prop
  have hβ : Measurable (fun x : Chart5 => x 4) := by fun_prop
  have hp : Measurable sourceEndpointA := by
    change Measurable (fun x : Chart5 => sourceCenter x + u (sourceCenter x) (x 3))
    apply Measurable.add hD
    exact hu.comp (hD.prodMk hα)
  have hq : Measurable sourceEndpointB := by
    change Measurable (fun x : Chart5 => sourceCenter x + v (sourceCenter x) (x 4))
    apply Measurable.add hD
    change Measurable ((fun z : Pt × ℝ => v z.1 z.2) ∘
      (fun x : Chart5 => (sourceCenter x,x 4)))
    exact hv.comp (hD.prodMk hβ)
  have hm : AEStronglyMeasurable (fun x => G (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) /
      (‖sourceCenter x‖ * ‖sourceCenter x-e‖)) (volume.restrict S) :=
    ((hG.comp (hD.prodMk (hp.prodMk hq))).div
      (hD.norm.mul (hD.sub measurable_const).norm)).aestronglyMeasurable.restrict
  refine hdom.integrableOn.mono' hm ?_
  filter_upwards [ae_restrict_mem hSm] with x hx
  rcases hS x hx with ⟨hxl,hxα,hxβ,hxp,hxq,hdp,hdq,hz0,hz1⟩
  have hgb := hb (sourceCenter x) hxl (sourceEndpointA x) hxp (sourceEndpointB x) hxq hdp hdq hz0 hz1
  have ha := norm_nonneg (sourceCenter x)
  have hbb := norm_nonneg (sourceCenter x-e)
  have hm0 : 0 ≤ (‖sourceCenter x‖ * ‖sourceCenter x-e‖)⁻¹ := inv_nonneg.mpr (mul_nonneg ha hbb)
  have hval : H (sourceCenter x,x 3,x 4) = C * (‖sourceCenter x‖ * ‖sourceCenter x-e‖)⁻¹ := by
    simp [H,bD,bθ,I,Set.indicator_of_mem,hxl,hxα,hxβ]
  rw [hval]
  calc
    ‖G (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) /
      (‖sourceCenter x‖ * ‖sourceCenter x-e‖)‖ =
      |G (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x)| *
        (‖sourceCenter x‖ * ‖sourceCenter x-e‖)⁻¹ := by
      rw [div_eq_mul_inv,norm_mul]
      simp [Real.norm_eq_abs,abs_of_nonneg hm0]
    _ ≤ C * (‖sourceCenter x‖ * ‖sourceCenter x-e‖)⁻¹ := mul_le_mul_of_nonneg_right hgb hm0

