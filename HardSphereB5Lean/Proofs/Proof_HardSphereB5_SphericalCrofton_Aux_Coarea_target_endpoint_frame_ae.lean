import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_coordinates_preserving
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_centerFrame_nonzero
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_chart5_ae_linear_ne
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_signed_endpoint_measures
set_option autoImplicit false
open MeasureTheory Set SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section
set_option maxHeartbeats 1000000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_endpoint_frame_ae :
    ∀ᵐ pq : Pt × Pt ∂(((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)),
      centerFrame0 (pq.2-pq.1) ≠ 0 := by
  let SA : Set (ℝ × ℝ) := Icc (1/2 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi
  let SB : Set (ℝ × ℝ) := Icc (-1 : ℝ) (-1/2) ×ˢ Icc (-Real.pi) Real.pi
  let μA : Measure (ℝ × ℝ) := volume.restrict SA
  let μB : Measure (ℝ × ℝ) := volume.restrict SB
  let μψ : Measure ℝ := volume.restrict (Icc (-Real.pi) Real.pi)
  let A : ℝ × ℝ → Pt := fun a => endpointCylinder a.1 a.2
  let B : ℝ × ℝ → Pt := fun b => e+endpointCylinder b.1 b.2
  let F : (ℝ × ℝ) × (ℝ × ℝ) → Pt × Pt := Prod.map A B
  have hA : Measurable A := by dsimp [A,endpointCylinder]; fun_prop
  have hB : Measurable B := by dsimp [B,endpointCylinder]; fun_prop
  have hF : Measurable F := hA.prodMap hB
  have hFm : Measurable (fun pq : Pt × Pt => centerFrame0 (pq.2-pq.1)) := by
    dsimp [centerFrame0,unitDir]
    fun_prop
  have hP : MeasurableSet {pq : Pt × Pt | centerFrame0 (pq.2-pq.1) ≠ 0} :=
    (measurableSet_eq_fun hFm measurable_const).compl
  have heval (i : Fin 5) (c : ℝ) : ∀ᵐ y : Chart5 ∂volume, y i ≠ c := by
    let L : Chart5 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ i
    have hL : L ≠ 0 := by
      intro h
      have hh := congrArg (fun f : Chart5 →ₗ[ℝ] ℝ => f (EuclideanSpace.single i (1 : ℝ))) h
      norm_num [L,EuclideanSpace.projₗ,PiLp.projₗ] at hh
    exact chart5_ae_linear_ne L hL c
  have hdiag : ∀ᵐ y : Chart5 ∂volume, y 1 ≠ y 3 := by
    let L : Chart5 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1-EuclideanSpace.projₗ 3
    have hL : L ≠ 0 := by
      intro h
      have hh := congrArg (fun f : Chart5 →ₗ[ℝ] ℝ => f (EuclideanSpace.single (1 : Fin 5) (1 : ℝ))) h
      norm_num [L,EuclideanSpace.projₗ,PiLp.projₗ,show (3 : Fin 5) ≠ 1 by decide] at hh
    have h := chart5_ae_linear_ne L hL 0
    change ∀ᵐ y : Chart5 ∂volume, y 1-y 3 ≠ 0 at h
    simpa only [sub_ne_zero] using h
  let P : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) → Prop := fun w =>
    w.1.1 ∈ SA ∧ w.1.2 ∈ SB → centerFrame0 ((F w.1).2-(F w.1).1) ≠ 0
  have hPm : MeasurableSet {w | P w} := by
    rw [show {w | P w} = ({w : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) | w.1.1 ∈ SA ∧ w.1.2 ∈ SB}ᶜ ∪
      {w : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) | centerFrame0 ((F w.1).2-(F w.1).1) ≠ 0}) by
      ext w
      simp only [P,Set.mem_setOf_eq,Set.mem_union,Set.mem_compl_iff,imp_iff_not_or]]
    apply MeasurableSet.union
    · exact (((measurableSet_Icc.prod measurableSet_Icc).preimage
        (measurable_fst.comp measurable_fst)).inter
        ((measurableSet_Icc.prod measurableSet_Icc).preimage
          (measurable_snd.comp measurable_fst))).compl
    · exact hP.preimage (hF.comp measurable_fst)
  have hchart : ∀ᵐ y : Chart5 ∂volume, P (((y 0,y 1),(y 2,y 3)),y 4) := by
    filter_upwards [heval 0 1,heval 2 (-1),heval 1 (-Real.pi),heval 1 Real.pi,
      heval 3 (-Real.pi),heval 3 Real.pi,hdiag] with y hy0 hy2 hy10 hy11 hy30 hy31 hy13
    rintro ⟨hSA,hSB⟩
    apply target_centerFrame_nonzero y
    · exact abs_lt.mpr ⟨by linarith [hSA.1.1],lt_of_le_of_ne hSA.1.2 hy0⟩
    · exact abs_lt.mpr ⟨lt_of_le_of_ne hSB.1.1 hy2.symm,by linarith [hSB.1.2]⟩
    · exact ⟨lt_of_le_of_ne hSA.2.1 hy10.symm,lt_of_le_of_ne hSA.2.2 hy11⟩
    · exact ⟨lt_of_le_of_ne hSB.2.1 hy30.symm,lt_of_le_of_ne hSB.2.2 hy31⟩
    · exact hy13
  have hprod : ∀ᵐ w ∂(volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ)), P w := by
    rw [← target_coordinates_preserving.map_eq]
    exact (ae_map_iff target_coordinates_preserving.aemeasurable hPm).2 hchart
  have hrect : (μA.prod μB).prod μψ =
      (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ)).restrict
        ((SA ×ˢ SB) ×ˢ Icc (-Real.pi) Real.pi) := by
    dsimp [μA,μB,μψ]
    rw [Measure.prod_restrict,Measure.prod_restrict]
    rfl
  have htrip : ∀ᵐ w ∂((μA.prod μB).prod μψ), centerFrame0 ((F w.1).2-(F w.1).1) ≠ 0 := by
    rw [hrect]
    filter_upwards [ae_restrict_of_ae hprod,
      ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc).prod
        (measurableSet_Icc.prod measurableSet_Icc) |>.prod measurableSet_Icc)] with w hp hw
    exact hp hw.1
  have hcoord : ∀ᵐ z ∂(μA.prod μB), centerFrame0 ((F z).2-(F z).1) ≠ 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod htrip] with z hz
    have hv : volume (Icc (-Real.pi) Real.pi) ≠ 0 := by
      rw [Real.volume_Icc,ENNReal.ofReal_ne_zero_iff]
      linarith [Real.pi_pos]
    obtain ⟨ψ,_,hψ⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hv hz
    exact hψ
  rw [signed_endpoint_measures.1,signed_endpoint_measures.2,
    Measure.map_prod_map _ _ hA hB]
  exact (ae_map_iff hF.aemeasurable hP).2 hcoord
