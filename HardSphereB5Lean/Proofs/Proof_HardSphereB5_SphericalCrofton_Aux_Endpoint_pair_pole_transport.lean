import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_endpoint_radial_chart_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_counted_jacobian_map
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_pole_transport (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) :
    (weightedPairMu D).map pairPole = dOmega.restrict (hitPoleSet D) := by
  obtain ⟨Φ,Φ',P,s,hΦ,hΦ',hP,hs,hHit,hder,hdir,hcount,hparam⟩ :=
    endpoint_radial_chart_data D hD hK
  let N : Pt → Pt := fun y => ‖y‖⁻¹ • y
  let H : Set Pt := Metric.ball (0:Pt) 1 ∩ N ⁻¹' hitPoleSet D
  let μs : Measure Pt := (volume.restrict s).withDensity (fun x => ENNReal.ofReal |(Φ' x).det|)
  have hN : Measurable N := by dsimp [N]; fun_prop
  have hH : MeasurableSet H := Metric.isOpen_ball.measurableSet.inter (hN hHit)
  have harea : μs.map Φ = volume.restrict H :=
    counted_jacobian_map volume Φ Φ' s H hΦ hs hH hΦ' hder hcount
  have hmem0 : ∀ᵐ x ∂(volume.restrict s), x ∈ s := ae_restrict_mem hs
  have hmem : ∀ᵐ x ∂μs, x ∈ s :=
    (withDensity_absolutelyContinuous _ _).ae_le hmem0
  have hmap : μs.map (N ∘ Φ) = μs.map (pairPole ∘ P) := by
    apply Measure.map_congr
    filter_upwards [hmem] with x hx
    exact hdir x hx
  have hp : Measurable pairPole := (pair_measurable D).2.2.2.1
  have hdO := SphereGeom.Aux.Crofton.dOmega_eq_three_smul_map_radial
  have hball : (volume.restrict H).map N =
      (3:ENNReal)⁻¹ • dOmega.restrict (hitPoleSet D) := by
    have hc : (volume.restrict H).map N =
        ((volume.restrict (Metric.ball (0:Pt) 1)).map N).restrict (hitPoleSet D) := by
      rw [Measure.restrict_map hN hHit, Measure.restrict_restrict (hN hHit), Set.inter_comm]
    rw [hc]
    have hbase : ((volume.restrict (Metric.ball (0:Pt) 1)).map N) = (3:ENNReal)⁻¹ • dOmega := by
      rw [hdO]
      rw [smul_smul, ENNReal.inv_mul_cancel (by norm_num : (3:ENNReal)≠0) (by norm_num : (3:ENNReal)≠⊤), one_smul]
    rw [hbase, Measure.restrict_smul]
  have hscaled : (3:ENNReal)⁻¹ • (weightedPairMu D).map pairPole =
      (3:ENNReal)⁻¹ • dOmega.restrict (hitPoleSet D) := by
    calc
      (3:ENNReal)⁻¹ • (weightedPairMu D).map pairPole = (μs.map P).map pairPole := by
        rw [hparam, Measure.map_smul]
      _ = μs.map (pairPole ∘ P) := Measure.map_map hp hP
      _ = μs.map (N ∘ Φ) := hmap.symm
      _ = (μs.map Φ).map N := (Measure.map_map hN hΦ).symm
      _ = (volume.restrict H).map N := by rw [harea]
      _ = (3:ENNReal)⁻¹ • dOmega.restrict (hitPoleSet D) := hball
  have h := congrArg (fun μ : Measure Pt => (3:ENNReal) • μ) hscaled
  rw [smul_smul, smul_smul, ENNReal.mul_inv_cancel (by norm_num : (3:ENNReal)≠0) (by norm_num : (3:ENNReal)≠⊤), one_smul, one_smul] at h
  exact h
