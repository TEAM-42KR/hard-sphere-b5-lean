import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_volume_map
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_coord_two_zeros_finite
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_beta_cross_axis_zeros_finite
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_joint_measurable
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_trig_zeros_finite
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

set_option maxHeartbeats 800000
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_phase_generic_ae : ∀ᵐ x : Chart5 ∂volume,
    (sourceCenter x ∈ LamC ∧ x 3 ∈ Set.Icc (-Real.pi) Real.pi ∧ x 4 ∈ Set.Icc (-Real.pi) Real.pi) →
    (sourceEndpointA x) 2 ≠ 0 ∧ (sourceEndpointB x) 2 ≠ 0 ∧
      inner ℝ (cross (u (sourceCenter x) (x 3)) (v (sourceCenter x) (x 4))) e ≠ 0 := by
  let U : (Pt × (ℝ × ℝ)) → Pt := fun z => u z.1 z.2.1
  let V : (Pt × (ℝ × ℝ)) → Pt := fun z => v z.1 z.2.2
  let T : (Pt × (ℝ × ℝ)) → ℝ := fun z => inner ℝ (cross (U z) (V z)) e
  let P : (Pt × (ℝ × ℝ)) → Prop := fun z =>
    (z.1 ∈ LamC ∧ z.2.1 ∈ Set.Icc (-Real.pi) Real.pi ∧ z.2.2 ∈ Set.Icc (-Real.pi) Real.pi) →
      (z.1 + U z) 2 ≠ 0 ∧ (z.1 + V z) 2 ≠ 0 ∧ T z ≠ 0
  have hU : Measurable U := joint_measurable.1.comp (measurable_fst.prodMk measurable_snd.fst)
  have hVB : Measurable (fun z : Pt × (ℝ × ℝ) => (z.1, z.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  have hV : Measurable V := by
    change Measurable ((fun q : Pt × ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.v q.1 q.2) ∘
      (fun z : Pt × (ℝ × ℝ) => (z.1, z.2.2)))
    exact joint_measurable.2.1.comp hVB
  have hcoord (i : Fin 3) : Measurable (fun p : Pt => p i) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) i).measurable
  have hT : Measurable T := by
    have htr (a b : Pt) : inner ℝ (cross a b) e = a 1 * b 2 - a 2 * b 1 := by
      simp [PiLp.inner_apply, Fin.sum_univ_succ, HardSphereB5.Lean.e, cross, cross_apply]
    have heq : T = fun z => (U z) 1 * (V z) 2 - (U z) 2 * (V z) 1 :=
      funext (fun z => htr (U z) (V z))
    rw [heq]
    exact ((hcoord 1 |>.comp hU).mul (hcoord 2 |>.comp hV)).sub
      ((hcoord 2 |>.comp hU).mul (hcoord 1 |>.comp hV))
  have hPA : Measurable (fun z : Pt × (ℝ × ℝ) => (z.1 + U z) 2) :=
    (hcoord 2).comp (measurable_fst.add hU)
  have hPB : Measurable (fun z : Pt × (ℝ × ℝ) => (z.1 + V z) 2) :=
    (hcoord 2).comp (measurable_fst.add hV)
  have hL : MeasurableSet LamC := measurableSet_closedBall.inter measurableSet_closedBall
  have hP : MeasurableSet {z | P z} := by
    dsimp only [P]
    measurability
  have hDN (i : Fin 3) : ∀ᵐ D : Pt ∂volume, D i ≠ 0 := by
    have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).quasiMeasurePreserving.ae
      (Measure.ae_eval_ne (μ := fun _ : Fin 3 => (volume : Measure ℝ)) i (0 : ℝ))
    exact h
  have hsin : ∀ᵐ α : ℝ ∂volume, α ∈ Set.Icc (-Real.pi) Real.pi → Real.sin α ≠ 0 := by
    have hz := SphereGeom.Aux.Arrangement.trig_zeros_finite
      0 1 0 (-Real.pi) Real.pi (Or.inr (Or.inl one_ne_zero))
    filter_upwards [hz.countable.ae_notMem (volume : Measure ℝ)] with α hα hbound
    exact fun hs => hα ⟨hbound, by simpa using hs⟩
  have hnest : ∀ᵐ D : Pt ∂volume, ∀ᵐ α : ℝ ∂volume, ∀ᵐ β : ℝ ∂volume, P (D, (α, β)) := by
    filter_upwards [hDN 1, hDN 2] with D hD1 hD2
    have hoff : offAxis D := by
      intro t ht
      apply hD1
      rw [ht]
      simp [e]
    by_cases hLD : D ∈ LamC
    · have hends := endpoint_coord_two_zeros_finite D hD2
      filter_upwards [hsin, hends.1.countable.ae_notMem (volume : Measure ℝ)] with α hα hAz
      by_cases hαb : α ∈ Set.Icc (-Real.pi) Real.pi
      · have ht := beta_cross_axis_zeros_finite D hLD hoff hD1 α (hα hαb)
        filter_upwards [hends.2.countable.ae_notMem (volume : Measure ℝ),
          ht.countable.ae_notMem (volume : Measure ℝ)] with β hBz hTz
        intro hpre
        exact ⟨fun hz => hAz ⟨hαb, hz⟩,
          fun hz => hBz ⟨hpre.2.2, hz⟩, fun hz => hTz ⟨hpre.2.2, hz⟩⟩
      · exact Filter.Eventually.of_forall (fun β hpre => False.elim (hαb hpre.2.1))
    · exact Filter.Eventually.of_forall (fun α => Filter.Eventually.of_forall
        (fun β hpre => False.elim (hLD hpre.1)))
  have hprod : ∀ᵐ z : Pt × (ℝ × ℝ) ∂volume.prod (volume.prod volume), P z := by
    apply (Measure.ae_prod_iff_ae_ae hP).mpr
    filter_upwards [hnest] with D hD
    have hPs : MeasurableSet {q : ℝ × ℝ | P (D, q)} :=
      hP.preimage (measurable_const.prodMk measurable_id)
    exact (Measure.ae_prod_iff_ae_ae hPs).mpr hD
  have hout := source_volume_map.quasiMeasurePreserving.ae hprod
  exact hout
