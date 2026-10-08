import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean Set
private abbrev E3 := Pt
set_option maxHeartbeats 1000000

private theorem capCertificate (c n : E3) (hn : ‖n‖ = 1) (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (volume {x | x ∈ Metric.closedBall c 1 ∧ t ≤ inner ℝ n (x - c)}).toReal =
      π * (1 - t) ^ 2 * (2 + t) / 3 := by
  classical
  let a : E3 := EuclideanSpace.single 0 1
  let s : Set E3 := {x | x ∈ Metric.closedBall 0 1 ∧ t ≤ inner ℝ a x}
  have hm : MeasurableSet s := by
    exact measurableSet_closedBall.inter (measurableSet_le measurable_const
      (by fun_prop : Measurable (fun x : E3 => inner ℝ a x)))
  have hsplit : (volume s).toReal = ∫ z : ℝ,
      (volume {y : Fin 2 → ℝ | WithLp.toLp 2 (Fin.cons z y) ∈ s}).toReal := by
    let f : E3 → ℝ := s.indicator (fun _ => 1)
    let E := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (0 : Fin 3)).symm
    have hf : volume s ≠ ⊤ :=
      measure_ne_top_of_subset (fun x hx => hx.1) measure_closedBall_lt_top.ne
    have hi : Integrable f := by
      apply (integrable_indicator_iff hm).2
      exact integrableOn_const hf
    have hp : MeasurePreserving (fun p : ℝ × (Fin 2 → ℝ) => WithLp.toLp 2 (E p)) :=
      (PiLp.volume_preserving_toLp (Fin 3)).comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
    have heq (z : ℝ) (y : Fin 2 → ℝ) : E (z,y) = Fin.cons z y := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [E, MeasurableEquiv.piFinSuccAbove]
    have hprod := integral_prod (f := fun p : ℝ × (Fin 2 → ℝ) => f (WithLp.toLp 2 (E p)))
      (hp.integrable_comp_of_integrable hi)
    have hc := hp.integral_comp
      ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding.comp E.measurableEmbedding) f
    change (∫ z, f (WithLp.toLp 2 (E z))) = _ at hprod
    rw [hc] at hprod
    change volume.real s = _
    rw [← integral_indicator_one hm]
    change (∫ x, f x) = _
    rw [hprod]
    apply integral_congr_ae
    filter_upwards [] with z
    simp_rw [heq]
    have hslice : MeasurableSet {y : Fin 2 → ℝ | WithLp.toLp 2 (Fin.cons z y) ∈ s} := by
      apply hm.preimage
      exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
        ((continuous_const.finCons continuous_id).measurable)
    change _ = volume.real {y : Fin 2 → ℝ | WithLp.toLp 2 (Fin.cons z y) ∈ s}
    rw [← integral_indicator_one hslice]
    congr 1
  have hdisk (z : ℝ) :
      (volume {y : Fin 2 → ℝ | WithLp.toLp 2 (Fin.cons z y) ∈ s}).toReal =
        if t ≤ z ∧ -1 ≤ z ∧ z ≤ 1 then π * (1 - z^2) else 0 := by
    have hnorm (y : Fin 2 → ℝ) :
        ‖(WithLp.toLp 2 (Fin.cons z y) : E3)‖ ^ 2 = z^2 +
          ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 2))‖^2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    have hc (y : Fin 2 → ℝ) : WithLp.toLp 2 (Fin.cons z y) ∈ s ↔
        z^2 + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 2))‖^2 ≤ 1 ∧ t ≤ z := by
      simp only [s, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
      have ha : inner ℝ a (WithLp.toLp 2 (Fin.cons z y)) = z := by
        simp [a, EuclideanSpace.inner_single_left]
      rw [ha, ← hnorm]
      constructor
      · rintro ⟨h, ht⟩
        exact ⟨by nlinarith [norm_nonneg (WithLp.toLp 2 (Fin.cons z y) : E3)], ht⟩
      · rintro ⟨h, ht⟩
        exact ⟨by nlinarith [norm_nonneg (WithLp.toLp 2 (Fin.cons z y) : E3)], ht⟩
    by_cases hz : t ≤ z ∧ -1 ≤ z ∧ z ≤ 1
    · rw [if_pos hz]
      have hq : 0 ≤ 1-z^2 := by
        nlinarith [mul_nonneg (show 0 ≤ 1-z by linarith [hz.2.2])
          (show 0 ≤ 1+z by linarith [hz.2.1])]
      have hs : {y : Fin 2 → ℝ | WithLp.toLp 2 (Fin.cons z y) ∈ s} =
          (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (√(1-z^2)) := by
        ext y
        rw [Set.mem_setOf_eq, hc]
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
        have hsq := Real.sq_sqrt hq
        have hn0 := norm_nonneg (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 2))
        have hr := Real.sqrt_nonneg (1-z^2)
        constructor
        · rintro ⟨h, _⟩; nlinarith
        · intro h; exact ⟨by nlinarith, hz.1⟩
      rw [hs, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
        measurableSet_closedBall.nullMeasurableSet]
      rw [EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (sqrt_nonneg _),
        ENNReal.toReal_ofReal pi_nonneg, sq_sqrt hq]
      ring
    · rw [if_neg hz]
      have hs : {y : Fin 2 → ℝ | WithLp.toLp 2 (Fin.cons z y) ∈ s} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        rw [Set.mem_setOf_eq, hc] at hy
        apply hz
        exact ⟨hy.2, by nlinarith [sq_nonneg ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 2))‖],
          by nlinarith [sq_nonneg ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 2))‖]⟩
      simp [hs]
  have hbase : (volume s).toReal = π * (1-t)^2 * (2+t) / 3 := by
    rw [hsplit]
    simp_rw [hdisk]
    have hi (z : ℝ) :
        (if t ≤ z ∧ -1 ≤ z ∧ z ≤ 1 then π*(1-z^2) else 0) =
          (Icc t 1).indicator (fun z => π*(1-z^2)) z := by
      by_cases hz : z ∈ Icc t 1
      · rw [Set.indicator_of_mem hz, if_pos ⟨hz.1, le_trans ht0 hz.1, hz.2⟩]
      · rw [Set.indicator_of_notMem hz, if_neg (by intro h; exact hz ⟨h.1,h.2.2⟩)]
    simp_rw [hi]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht1, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const, integral_pow, smul_eq_mul]
      norm_num
      ring
    · exact intervalIntegrable_const
    · exact (continuous_id.pow 2).intervalIntegrable _ _
  let R : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ (a-n))ᗮ.reflection
  have hR : R a = n := by
    exact Submodule.reflection_sub (by simpa [a] using hn.symm)
  have hmp : MeasurePreserving (fun x : E3 => c + R x) volume volume :=
    (measurePreserving_add_left volume c).comp R.measurePreserving
  have hpre : (fun x : E3 => c + R x) ⁻¹'
      {x | x ∈ Metric.closedBall c 1 ∧ t ≤ inner ℝ n (x-c)} = s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm,
      add_sub_cancel_left, R.norm_map, s, sub_zero]
    rw [← hR, R.inner_map_map]
  have hmcap : MeasurableSet {x : E3 | x ∈ Metric.closedBall c 1 ∧ t ≤ inner ℝ n (x-c)} := by
    exact measurableSet_closedBall.inter (measurableSet_le measurable_const
      (by fun_prop : Measurable (fun x : E3 => inner ℝ n (x-c))))
  have hv := hmp.measure_preimage hmcap.nullMeasurableSet
  rw [hpre] at hv
  rw [← hv]
  exact hbase

private theorem plane_null (c n : E3) (hn : ‖n‖ = 1) (t : ℝ) :
    volume {z : E3 | inner ℝ n (z - c) = t} = 0 := by
  let K := (innerSL ℝ n).toLinearMap.ker
  have hi : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hk : K ≠ ⊤ := by
    intro h
    have hmem : n ∈ K := by rw [h]; trivial
    change inner ℝ n n = 0 at hmem
    linarith
  have hs : {z : E3 | inner ℝ n (z - c) = t} =
      (fun z => z + (-(c + t • n))) ⁻¹' (K : Set E3) := by
    ext z
    change inner ℝ n (z - c) = t ↔ inner ℝ n (z + -(c + t • n)) = 0
    simp only [inner_sub_right, inner_add_right, inner_neg_right, inner_smul_right, hi]
    simp only [mul_one]
    constructor <;> intro h <;> linarith
  rw [hs, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume K hk

private theorem closedLensCertificate (x y : E3) (h : dist x y ≤ 2) :
    (volume (Metric.closedBall x 1 ∩ Metric.closedBall y 1)).toReal =
      π * (4 / 3 - dist x y + dist x y ^ 3 / 12) := by
  by_cases hxy : x = y
  · subst y
    rw [inter_self, EuclideanSpace.volume_closedBall_fin_three]
    simp only [dist_self, ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal
      (show 0 ≤ π * 4 / 3 by positivity)]
    ring
  let d := dist x y
  have hd : 0 < d := dist_pos.mpr hxy
  let n : E3 := d⁻¹ • (y - x)
  have hdn : d • n = y - x := by
    dsimp [n]
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  have hnorm : ‖y-x‖ = d := by dsimp [d]; rw [dist_eq_norm, norm_sub_rev]
  have hn : ‖n‖ = 1 := by
    dsimp [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), hnorm,
      inv_mul_cancel₀ hd.ne']
  have hi : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hsq (z : E3) : ‖z-y‖^2 = ‖z-x‖^2 - 2*d*inner ℝ n (z-x) + d^2 := by
    have hv : z-y = (z-x) - d • n := by rw [hdn]; abel
    rw [hv, norm_sub_sq_real, inner_smul_right, real_inner_comm (z-x) n,
      norm_smul, Real.norm_eq_abs, abs_of_pos hd, hn]
    ring
  have hip (z : E3) : inner ℝ (-n) (z-y) = d - inner ℝ n (z-x) := by
    have hv : z-y = (z-x) - d • n := by rw [hdn]; abel
    rw [hv, inner_neg_left, inner_sub_right, inner_smul_right, hi]
    ring
  let A : Set E3 := {z | z ∈ Metric.closedBall x 1 ∧ d/2 ≤ inner ℝ n (z-x)}
  let B : Set E3 := {z | z ∈ Metric.closedBall y 1 ∧ d/2 ≤ inner ℝ (-n) (z-y)}
  have hu : A ∪ B = Metric.closedBall x 1 ∩ Metric.closedBall y 1 := by
    ext z
    have hnx := norm_nonneg (z-x)
    have hny := norm_nonneg (z-y)
    have hx : z ∈ Metric.closedBall x 1 ↔ ‖z-x‖^2 ≤ 1 := by
      simp only [Metric.mem_closedBall, dist_eq_norm]
      constructor <;> intro hz <;> nlinarith
    have hy : z ∈ Metric.closedBall y 1 ↔ ‖z-y‖^2 ≤ 1 := by
      simp only [Metric.mem_closedBall, dist_eq_norm]
      constructor <;> intro hz <;> nlinarith
    change (z ∈ Metric.closedBall x 1 ∧ d/2 ≤ inner ℝ n (z-x)) ∨
      (z ∈ Metric.closedBall y 1 ∧ d/2 ≤ inner ℝ (-n) (z-y)) ↔
      z ∈ Metric.closedBall x 1 ∧ z ∈ Metric.closedBall y 1
    rw [hx, hy, hip]
    constructor
    · rintro (⟨hz, ha⟩ | ⟨hz, hb⟩)
      · exact ⟨hz, by nlinarith [hsq z]⟩
      · exact ⟨by nlinarith [hsq z], hz⟩
    · rintro ⟨hx,hy⟩
      by_cases ha : d/2 ≤ inner ℝ n (z-x)
      · exact Or.inl ⟨hx,ha⟩
      · exact Or.inr ⟨hy, by linarith⟩
  have hmB : MeasurableSet B := by
    apply measurableSet_closedBall.inter
    exact measurableSet_le measurable_const
      ((continuous_const.inner (𝕜 := ℝ) ((continuous_id : Continuous (fun z : E3 => z)).sub continuous_const)).measurable)
  have htA : volume A ≠ ⊤ := measure_ne_top_of_subset
    (show A ⊆ Metric.closedBall x 1 from fun z hz => hz.1) measure_closedBall_lt_top.ne
  have htB : volume B ≠ ⊤ := measure_ne_top_of_subset
    (show B ⊆ Metric.closedBall y 1 from fun z hz => hz.1) measure_closedBall_lt_top.ne
  have hzero : volume (A ∩ B) = 0 := by
    apply measure_mono_null _ (plane_null x n hn (d/2))
    intro z hz
    change inner ℝ n (z-x) = d/2
    have ha := hz.1.2
    have hb := hz.2.2
    rw [hip] at hb
    linarith
  have hv := measureReal_union_add_inter hmB htA htB
  simp only [Measure.real, hzero, ENNReal.toReal_zero, add_zero, hu] at hv
  have ht0 : -1 ≤ d/2 := by linarith
  have ht1 : d/2 ≤ 1 := by change d ≤ 2 at h; linarith
  have hnneg : ‖-n‖ = 1 := by simpa using hn
  have hA := capCertificate x n hn (d/2) ht0 ht1
  have hB := capCertificate y (-n) hnneg (d/2) ht0 ht1
  change (volume A).toReal = _ at hA
  change (volume B).toReal = _ at hB
  change (volume (Metric.closedBall x 1 ∩ Metric.closedBall y 1)).toReal =
    (volume A).toReal + (volume B).toReal at hv
  rw [hv, hA, hB]
  change _ = π * (4/3-d+d^3/12)
  ring

private theorem openLensCertificate (x y : E3) (h : dist x y ≤ 2) :
    (volume (Metric.ball x 1 ∩ Metric.ball y 1)).toReal =
      π * (4 / 3 - dist x y + dist x y ^ 3 / 12) := by
  have hae (c : E3) : Metric.ball c 1 =ᵐ[volume] Metric.closedBall c 1 :=
    ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume c 1).le
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  rw [measure_congr (ae_eq_set_inter (hae x) (hae y))]
  exact closedLensCertificate x y h

theorem proof_HardSphereB5_Lean_Geometry_lensVolFormula (l : ℝ) (h0 : 0 ≤ l) (h2 : l ≤ 2) :
    lensVol l = π / 12 * (2 - l) ^ 2 * (4 + l) := by
  have he : ‖e‖ = 1 := by simp [e]
  have hd : dist (0 : Pt) (l • e) = l := by
    rw [dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, he, mul_one]
  have hv := openLensCertificate (0 : Pt) (l • e) (by simpa only [hd] using h2)
  change (volume (Metric.ball (0 : Pt) 1 ∩ Metric.ball (l • e) 1)).toReal = _
  rw [hv, hd]
  ring

#print axioms proof_HardSphereB5_Lean_Geometry_lensVolFormula
