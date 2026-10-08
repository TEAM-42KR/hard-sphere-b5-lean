import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_arc_pullback
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_inactive_source_zero
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_integral_reduction (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2)) :
    (∫ D in LamC, ∫ U in arcA D, ∫ V in arcB D,
      (if 0 < dist (D+U) (D+V) ∧ dist (D+U) (D+V) < 1 then
        G D (D+U) (D+V) / (‖D‖ * ‖D-e‖ * rA D * rB D) else 0)
        ∂arcMeasure ∂arcMeasure) =
    ∫ D in LamC, if offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1 then
      ∫ α in Set.Icc (-(halfA D)) (halfA D),
        ∫ β in Set.Icc (-(halfB D)) (halfB D),
          (if 0 < dist (D+u D α) (D+v D β) ∧ dist (D+u D α) (D+v D β) < 1
            then G D (D+u D α) (D+v D β) / (‖D‖ * ‖D-e‖) else 0)
      else 0  := by
  have hL : MeasurableSet LamC := (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).measurableSet
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hL] with D hD
  by_cases hact : offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1
  · rw [if_pos hact]
    let K : Pt → Pt → ℝ := fun p q => if 0 < dist p q ∧ dist p q < 1 then G D p q else 0
    have hm : Measurable (Function.uncurry K) := by
      have hk : Measurable (fun x : Pt × Pt => G D x.1 x.2) :=
        hG.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
      have hd : Measurable (fun x : Pt × Pt => dist x.1 x.2) :=
        (continuous_fst.dist continuous_snd).measurable
      have hs : MeasurableSet {x : Pt × Pt | 0 < dist x.1 x.2 ∧ dist x.1 x.2 < 1} :=
        (measurableSet_lt measurable_const hd).inter
        (measurableSet_lt hd measurable_const)
      exact hk.ite hs measurable_const
    have hp := HardSphereB5.SphericalCrofton.Aux.Coarea.source_arc_pullback D hD hact.1 hact.2 K hm
    simpa only [K, ite_div, zero_div] using hp
  · rw [if_neg hact]
    exact HardSphereB5.SphericalCrofton.Aux.Coarea.inactive_source_zero D hD hact _

