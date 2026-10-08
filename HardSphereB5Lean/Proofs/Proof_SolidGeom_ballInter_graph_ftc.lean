import HardSphereB5Lean.Theorems.Thm_SolidGeom_ballInter_slice_partition_ae
import HardSphereB5Lean.Theorems.Thm_SolidGeom_ballInter_strict_projection_ae
import HardSphereB5Lean.Theorems.Thm_SolidGeom_ballInter_graph_integrable
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped BigOperators Classical ENNReal

theorem proof_SolidGeom_ballInter_graph_ftc (n : ℕ) (hn : 0 < n) (c : Fin n → E3)
    (hc : Function.Injective c) (hK : (interior (⋂ i, Metric.closedBall (c i) 1)).Nonempty)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (a b : ℝ) :
    let K : Set E3 := ⋂ i, Metric.closedBall (c i) 1
    let D : Fin n → Set (ℝ × ℝ) := fun i => {p |
      (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let X : (ℝ × ℝ) → ℝ → E3 := fun p z => p.1 • e 0 + p.2 • e 1 + z • e 2
    (∑ i, ∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) -
      (∑ i, ∫ p in D i, if X p (l i p) ∈ K then a + b * l i p else 0) =
        b * (volume K).toReal := by
  classical
  let K : Set E3 := ⋂ i, Metric.closedBall (c i) 1
  let D : Fin n → Set (ℝ × ℝ) := fun i => {p |
    (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
  let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
    √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
    √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  let X : (ℝ × ℝ) → ℝ → E3 := fun p z => p.1 • e 0 + p.2 • e 1 + z • e 2
  let gU : Fin n → ℝ × ℝ → ℝ := fun i => (D i).indicator
    (fun p => if X p (u i p) ∈ K then a + b * u i p else 0)
  let gL : Fin n → ℝ × ℝ → ℝ := fun i => (D i).indicator
    (fun p => if X p (l i p) ∈ K then a + b * l i p else 0)
  let G : E3 → ℝ := K.indicator (fun _ => b)
  change (∑ i, ∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) -
    (∑ i, ∫ p in D i, if X p (l i p) ∈ K then a + b * l i p else 0) =
      b * (volume K).toReal
  have hKm : MeasurableSet K :=
    (isClosed_iInter (fun i => Metric.isClosed_closedBall (x := c i) (ε := 1))).measurableSet
  let i0 : Fin n := ⟨0, hn⟩
  have hKfin : volume K ≠ ∞ := ne_of_lt
    ((measure_mono (Set.iInter_subset (fun i => Metric.closedBall (c i) 1) i0)).trans_lt
      (isCompact_closedBall (c i0) 1).measure_lt_top)
  have hG : Integrable G := (integrableOn_const hKfin).integrable_indicator hKm
  have hDm (i : Fin n) : MeasurableSet (D i) := by
    exact measurableSet_lt (by fun_prop) measurable_const
  have hgi := SolidGeom.ballInter_graph_integrable n c e he a b
  have hgu (i : Fin n) : Integrable (gU i) :=
    (hgi i).1.integrable_indicator (hDm i)
  have hgl (i : Fin n) : Integrable (gL i) :=
    (hgi i).2.integrable_indicator (hDm i)
  have hsu : Integrable (fun p => ∑ i, gU i p) :=
    integrable_finset_sum Finset.univ (fun i _ => hgu i)
  have hsl : Integrable (fun p => ∑ i, gL i p) :=
    integrable_finset_sum Finset.univ (fun i _ => hgl i)
  have hlinear :
      (∑ i, ∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) -
        (∑ i, ∫ p in D i, if X p (l i p) ∈ K then a + b * l i p else 0) =
      ∫ p, (∑ i, gU i p) - (∑ i, gL i p) := by
    rw [integral_sub hsu hsl,
      integral_finset_sum _ (fun i _ => hgu i),
      integral_finset_sum _ (fun i _ => hgl i)]
    simp only [gU, gL, integral_indicator (hDm _)]
  have hae : (fun p => (∑ i, gU i p) - (∑ i, gL i p)) =ᵐ[volume]
      (fun p => ∫ z : ℝ, G (X p z)) := by
    filter_upwards [SolidGeom.ballInter_slice_partition_ae n hn c hc e he,
      SolidGeom.ballInter_strict_projection_ae n hn c e he] with p hpart hproj
    by_cases hp : ∀ i, p ∈ D i
    · obtain ⟨i, j, hbounds, hslice, hends⟩ := hpart hp
      change (∀ z : ℝ, X p z ∈ K ↔ z ∈ Set.Icc (l i p) (u j p)) at hslice
      have hsum := hends (fun z => a + b * z)
      change (∑ k, if u k p ∈ Set.Icc (l i p) (u j p) then a + b * u k p else 0) -
        (∑ k, if l k p ∈ Set.Icc (l i p) (u j p) then a + b * l k p else 0) =
        if l i p ≤ u j p then (a + b * u j p) - (a + b * l i p) else 0 at hsum
      have hup (k : Fin n) : gU k p =
          if u k p ∈ Set.Icc (l i p) (u j p) then a + b * u k p else 0 := by
        simp only [gU, Set.indicator_of_mem (hp k), hslice]
      have hlo (k : Fin n) : gL k p =
          if l k p ∈ Set.Icc (l i p) (u j p) then a + b * l k p else 0 := by
        simp only [gL, Set.indicator_of_mem (hp k), hslice]
      simp_rw [hup, hlo]
      rw [hsum]
      have hfiber : (fun z => G (X p z)) =
          (Set.Icc (l i p) (u j p)).indicator (fun _ => b) := by
        funext z
        simp only [G, Set.indicator_apply, hslice]
      rw [hfiber, integral_indicator_const b measurableSet_Icc]
      simp only [measureReal_def, Real.volume_Icc, smul_eq_mul]
      by_cases hle : l i p ≤ u j p
      · rw [if_pos hle, ENNReal.toReal_ofReal (sub_nonneg.mpr hle)]
        ring
      · rw [if_neg hle, ENNReal.ofReal_eq_zero.mpr
          (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hle)))]
        simp
    · have hnone (z : ℝ) : X p z ∉ K := by
        intro hz
        exact hp (hproj ⟨z, hz⟩)
      have hup (k : Fin n) : gU k p = 0 := by
        simp [gU, hnone]
      have hlo (k : Fin n) : gL k p = 0 := by
        simp [gL, hnone]
      simp only [hup, hlo, Finset.sum_const_zero, sub_zero]
      simp [G, hnone]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range e) :=
    (he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])).ge
  let basis : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk he hsp
  have hb : ∀ i, basis i = e i := fun i => congrFun (OrthonormalBasis.coe_mk he hsp) i
  let q : (Fin 3 → ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)
  have hq : MeasurePreserving q volume volume := by
    exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_finTwoArrow ℝ)).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
  have hqi : MeasurePreserving q.symm volume volume := hq.symm
  let T : ℝ × (ℝ × ℝ) → E3 := fun p => basis.repr.symm (WithLp.toLp 2 (q.symm p))
  have hT : MeasurePreserving T volume volume :=
    basis.measurePreserving_repr_symm.comp ((PiLp.volume_preserving_toLp (Fin 3)).comp hqi)
  have hTp (z x y : ℝ) : T (z, (x,y)) = x • e 0 + y • e 1 + z • e 2 := by
    dsimp [T]
    rw [← basis.sum_repr_symm, Fin.sum_univ_three]
    simp only [hb]
    simp [q, MeasurableEquiv.piFinSuccAbove_symm_apply,
      MeasurableEquiv.prodCongr, MeasurableEquiv.finTwoArrow_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth, Fin.succAboveCases, add_assoc]
  have hGT : Integrable (fun t => G (T t)) :=
    hT.integrable_comp_of_integrable hG
  have hmap : (∫ t, G (T t)) = ∫ x, G x := by
    have hGM : AEStronglyMeasurable G
        ((volume : Measure (ℝ × (ℝ × ℝ))).map T) := by
      simpa only [hT.map_eq] using hG.aestronglyMeasurable
    simpa only [hT.map_eq] using
      (integral_map hT.measurable.aemeasurable hGM).symm
  have hchart : (∫ p : ℝ × ℝ, ∫ z : ℝ, G (X p z)) = b * (volume K).toReal := by
    calc
      (∫ p : ℝ × ℝ, ∫ z : ℝ, G (X p z)) = ∫ t, G (T t) := by
        rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
        simpa only [hTp, X] using
          (integral_prod_symm (μ := (volume : Measure ℝ))
            (ν := (volume : Measure (ℝ × ℝ))) (fun t => G (T t)) hGT).symm
      _ = ∫ x, G x := hmap
      _ = b * (volume K).toReal := by
        rw [show (∫ x, G x) = volume.real K • b from
          integral_indicator_const b hKm]
        simp only [measureReal_def, smul_eq_mul, mul_comm]
  exact hlinear.trans ((integral_congr_ae hae).trans hchart)
