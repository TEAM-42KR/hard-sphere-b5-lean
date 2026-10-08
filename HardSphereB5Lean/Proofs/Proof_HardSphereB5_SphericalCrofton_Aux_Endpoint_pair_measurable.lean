import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable (D : Pt) : MeasurableSet (SigmaD D) ∧ MeasurableSet (arcA D) ∧
    MeasurableSet (arcB D) ∧ Measurable pairPole ∧ Measurable (pairDens D) ∧
      (∀ q, 0 ≤ pairDens D q) := by
  have hKc : IsClosed (SigmaD D) := by
    change IsClosed ({u : Pt | ‖u‖ = 1} ∩ (fun u : Pt => D+u) ⁻¹' LamC)
    apply IsClosed.inter (isClosed_eq continuous_norm continuous_const)
    exact ((Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0:Pt) 1)).inter Metric.isClosed_closedBall).preimage (by fun_prop)
  have hA : MeasurableSet (arcA D) := by
    by_cases hD : D=0
    · simp [arcA,hD]
    · unfold arcA
      rw [if_neg hD]
      exact (hKc.inter (isClosed_eq (by fun_prop) continuous_const)).measurableSet
  have hB : MeasurableSet (arcB D) := by
    by_cases hD : D=e
    · simp [arcB,hD]
    · unfold arcB
      rw [if_neg hD]
      exact (hKc.inter (isClosed_eq (by fun_prop) continuous_const)).measurableSet
  have hc : Measurable (fun q : Pt×Pt => cross q.1 q.2) := by
    unfold cross crossProduct
    fun_prop
  have hp : Measurable pairPole := by unfold pairPole unitDir; fun_prop
  have hta : Measurable (tanA D) := by
    have hcr : Measurable (fun u : Pt => cross (nAv D) u) :=
      hc.comp (measurable_const.prodMk measurable_id)
    unfold tanA unitDir
    fun_prop
  have htb : Measurable (tanB D) := by
    have hcr : Measurable (fun u : Pt => cross (nBv D) u) :=
      hc.comp (measurable_const.prodMk measurable_id)
    unfold tanB unitDir
    fun_prop
  have ht : Measurable (boundaryTau D) := hta.ite hA htb
  have hden : Measurable (pairDens D) := by
    unfold pairDens santaloDens
    fun_prop
  refine ⟨hKc.measurableSet,hA,hB,hp,hden,?_⟩
  intro q
  unfold pairDens santaloDens
  apply div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)) _
