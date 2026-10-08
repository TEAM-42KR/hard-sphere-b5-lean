import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_joint_measurable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical
set_option maxHeartbeats 1500000
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence_measurable : MeasurableSet sourceIncidence  := by
  have hD : Measurable sourceCenter := by unfold sourceCenter; fun_prop
  have hα : Measurable (fun x : Chart5 => x 3) := by fun_prop
  have hβ : Measurable (fun x : Chart5 => x 4) := by fun_prop
  rcases HardSphereB5.SphericalCrofton.Aux.MovingArc.joint_measurable with ⟨hu,hv,hha,hhb⟩
  have hp : Measurable sourceEndpointA := by
    change Measurable (fun x : Chart5 => sourceCenter x + u (sourceCenter x) (x 3))
    apply Measurable.add hD
    exact hu.comp (hD.prodMk hα)
  have hq : Measurable sourceEndpointB := by
    change Measurable (fun x : Chart5 => sourceCenter x + v (sourceCenter x) (x 4))
    apply Measurable.add hD
    change Measurable ((fun z : Pt × ℝ => v z.1 z.2) ∘ (fun x : Chart5 => (sourceCenter x,x 4)))
    exact hv.comp (hD.prodMk hβ)
  have hAxis : MeasurableSet {D : Pt | offAxis D} := by
    have hform (D : Pt) : offAxis D ↔ D 1 ≠ 0 ∨ D 2 ≠ 0 := by
      constructor
      · intro h
        by_contra hn
        push_neg at hn
        apply h (D 0)
        ext i
        fin_cases i <;> simp [e,hn.1,hn.2]
      · intro h t ht
        rcases h with h | h
        · have hc := congrArg (fun D : Pt => D 1) ht
          simp [e] at hc
          exact h hc
        · have hc := congrArg (fun D : Pt => D 2) ht
          simp [e] at hc
          exact h hc
    simp only [hform,Set.setOf_or]
    exact ((measurableSet_singleton (0 : ℝ)).preimage (by fun_prop : Measurable (fun D : Pt => D 1))).compl.union
      ((measurableSet_singleton (0 : ℝ)).preimage (by fun_prop : Measurable (fun D : Pt => D 2))).compl
  have hoff : MeasurableSet {x : Chart5 | offAxis (sourceCenter x)} := hAxis.preimage hD
  have hL : MeasurableSet LamC := (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).measurableSet
  have hFA : MeasurableSet FA := (Metric.isClosed_sphere.inter Metric.isClosed_closedBall).measurableSet
  have hFB : MeasurableSet FB := (Metric.isClosed_sphere.inter Metric.isClosed_closedBall).measurableSet
  have hR : Measurable (fun x : Chart5 => Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖) := by
    unfold Rc
    fun_prop
  have hRad : MeasurableSet {x : Chart5 | Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1} :=
    measurableSet_lt hR measurable_const
  have hAi : MeasurableSet {x : Chart5 | x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x))} :=
    (measurableSet_le (hha.comp hD).neg hα).inter (measurableSet_le hα (hha.comp hD))
  have hBi : MeasurableSet {x : Chart5 | x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x))} :=
    (measurableSet_le (hhb.comp hD).neg hβ).inter (measurableSet_le hβ (hhb.comp hD))
  have hz : Measurable (fun x : Chart5 => dist (sourceEndpointA x) (sourceEndpointB x)) := hp.dist hq
  have hz0 : MeasurableSet {x : Chart5 | 0 < dist (sourceEndpointA x) (sourceEndpointB x)} := measurableSet_lt measurable_const hz
  have hz1 : MeasurableSet {x : Chart5 | dist (sourceEndpointA x) (sourceEndpointB x) < 1} := measurableSet_lt hz measurable_const
  exact hoff.inter ((hL.preimage hD).inter (hRad.inter (hAi.inter (hBi.inter
    ((hFA.preimage hp).inter ((hFB.preimage hq).inter (hz0.inter hz1)))))))

