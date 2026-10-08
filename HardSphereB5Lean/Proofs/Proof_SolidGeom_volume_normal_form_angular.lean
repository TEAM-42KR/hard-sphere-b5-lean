import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

private theorem F8a.f1 (o : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e) (f : E3 → ENNReal)
    (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ φ in Set.Ioc (-π) π, ∫⁻ ρ in Set.Ioi (0 : ℝ), ∫⁻ z : ℝ,
      ENNReal.ofReal ρ * f (o + (ρ * cos φ) • e 0 + (ρ * sin φ) • e 1 + z • e 2) := by
  classical
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range e) :=
    (he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])).ge
  let b : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk he hsp
  have hb : ∀ i, b i = e i := fun i => congrFun (OrthonormalBasis.coe_mk he hsp) i
  let q : (Fin 3 → ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)
  have hq : MeasurePreserving q volume volume := by
    exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_finTwoArrow ℝ)).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
  have hqi : MeasurePreserving q.symm volume volume := hq.symm
  let T : ℝ × (ℝ × ℝ) → E3 := fun p => o + b.repr.symm (WithLp.toLp 2 (q.symm p))
  have hT : MeasurePreserving T volume volume :=
    (measurePreserving_add_left volume o).comp
      (b.measurePreserving_repr_symm.comp ((PiLp.volume_preserving_toLp (Fin 3)).comp hqi))
  have hTf : Measurable (fun p => f (T p)) := hf.comp hT.measurable
  have hTp (z x y : ℝ) : T (z, (x,y)) = o + x • e 0 + y • e 1 + z • e 2 := by
    dsimp [T]
    rw [← b.sum_repr_symm, Fin.sum_univ_three]
    simp only [hb]
    simp [q, MeasurableEquiv.piFinSuccAbove_symm_apply,
      MeasurableEquiv.prodCongr, MeasurableEquiv.finTwoArrow_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth, Fin.succAboveCases, add_assoc]
  let F : ℝ × ℝ → ENNReal := fun p => ∫⁻ z : ℝ, f (T (z,p))
  have hF : Measurable F := hTf.lintegral_prod_left'
  let H : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal p.1 * F (polarCoord.symm p)
  have hH : Measurable H :=
    (measurable_fst.ennreal_ofReal).mul (hF.comp continuous_polarCoord_symm.measurable)
  calc
    ∫⁻ x, f x = ∫⁻ p : ℝ × (ℝ × ℝ), f (T p) := (hT.lintegral_comp hf).symm
    _ = ∫⁻ p : ℝ × ℝ, F p := lintegral_prod_symm _ hTf.aemeasurable
    _ = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π, H p := by
      simpa [H, smul_eq_mul] using (lintegral_comp_polarCoord_symm F).symm
    _ = ∫⁻ ρ in Set.Ioi (0 : ℝ), ∫⁻ φ in Set.Ioo (-π) π, H (ρ,φ) :=
      setLIntegral_prod _ hH.aemeasurable
    _ = ∫⁻ φ in Set.Ioo (-π) π, ∫⁻ ρ in Set.Ioi (0 : ℝ), H (ρ,φ) :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ φ in Set.Ioc (-π) π, ∫⁻ ρ in Set.Ioi (0 : ℝ), H (ρ,φ) := by
      rw [restrict_Ioo_eq_restrict_Ioc]
    _ = _ := by
      apply lintegral_congr
      intro φ
      apply lintegral_congr
      intro ρ
      dsimp [H, F]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [show polarCoord.symm (ρ, φ) = (ρ * cos φ, ρ * sin φ) from rfl,
        hTp z (ρ * cos φ) (ρ * sin φ)]

private theorem F8a.f2 (m : ℝ) : volume {z : ℝ | z ^ 2 ≤ m} = ENNReal.ofReal (2 * √m) := by
  by_cases hm : 0 ≤ m
  · have hs : {z : ℝ | z ^ 2 ≤ m} = Set.Icc (-√m) √m := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      have hr := Real.sq_sqrt hm
      have hp := Real.sqrt_nonneg m
      constructor
      · intro h
        constructor <;> nlinarith
      · rintro ⟨h1, h2⟩
        nlinarith
    rw [hs, Real.volume_Icc]
    congr 1
    ring
  · have hm' : m < 0 := lt_of_not_ge hm
    have hs : {z : ℝ | z ^ 2 ≤ m} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      nlinarith [sq_nonneg z]
    rw [hs, measure_empty, Real.sqrt_eq_zero_of_nonpos (le_of_lt hm')]
    simp

private theorem F8a.f3 (h p : ℝ) (hh : 0 < h) :
    ∫ ρ in Set.Ioi (0 : ℝ), 2 * ρ * √(h ^ 2 - ρ ^ 2 - 2 * p * ρ) =
      2 / 3 * h ^ 3 + p ^ 2 * h - p * (h ^ 2 + p ^ 2) * (π / 2 - arctan (p / h)) := by
  let q : ℝ := √(h ^ 2 + p ^ 2)
  have hq : 0 < q := sqrt_pos.2 (by nlinarith [sq_nonneg p])
  have hq2 : q ^ 2 = h ^ 2 + p ^ 2 := sq_sqrt (by positivity)
  have hp1 : -q < p := by nlinarith [sq_pos_of_pos hh]
  have hp2 : p < q := by nlinarith [sq_pos_of_pos hh]
  let b : ℝ := q - p
  have hb : 0 < b := sub_pos.2 hp2
  let s : ℝ → ℝ := fun x => √(q ^ 2 - x ^ 2)
  let P : ℝ → ℝ := fun x => -(2 / 3) * (s x) ^ 3 -
    p * (x * s x + q ^ 2 * arcsin (x / q))
  have hnorm (x : ℝ) (hx : 0 ≤ q ^ 2 - x ^ 2) : √(1 - (x / q) ^ 2) = s x / q := by
    have he : 1 - (x / q) ^ 2 = (q ^ 2 - x ^ 2) / q ^ 2 := by
      field_simp
      <;> ring
    rw [he, sqrt_div hx, sqrt_sq hq.le]
  have hder (x : ℝ) (hx1 : -q < x) (hx2 : x < q) :
      HasDerivAt P (2 * (x - p) * s x) x := by
    have hin : 0 < q ^ 2 - x ^ 2 := by nlinarith
    have hs : 0 < s x := sqrt_pos.2 hin
    have hs2 : (s x) ^ 2 = q ^ 2 - x ^ 2 := sq_sqrt hin.le
    have hxq1 : x / q ≠ -1 := by
      apply ne_of_gt
      apply (lt_div_iff₀ hq).2
      linarith
    have hxq2 : x / q ≠ 1 := by
      apply ne_of_lt
      apply (div_lt_iff₀ hq).2
      simpa using hx2
    have d0 : HasDerivAt (fun y : ℝ => q ^ 2 - y ^ 2) (-2 * x) x := by
      convert! (hasDerivAt_id x).pow 2 |>.const_sub (q ^ 2) using 1 <;> simp [id_eq] <;> ring
    have ds : HasDerivAt s (-x / s x) x := by
      convert! d0.sqrt hin.ne' using 1
      dsimp [s]
      ring
    have da : HasDerivAt (fun y : ℝ => arcsin (y / q)) (1 / s x) x := by
      convert! (hasDerivAt_arcsin hxq1 hxq2).comp x ((hasDerivAt_id x).div_const q) using 1
      rw [hnorm x hin.le]
      field_simp
    have ds3 : HasDerivAt (fun y => (s y) ^ 3) (-3 * x * s x) x := by
      convert! ds.pow 3 using 1
      field_simp
      <;> ring
    have dt : HasDerivAt (fun y => y * s y + q ^ 2 * arcsin (y / q)) (2 * s x) x := by
      convert! ((hasDerivAt_id x).mul ds).add (da.const_mul (q ^ 2)) using 1
      simp only [id_eq]
      field_simp
      nlinarith [hs2]
    convert! (ds3.const_mul (-(2 / 3 : ℝ))).sub (dt.const_mul p) using 1 <;> (try dsimp [P]) <;> ring
  let f : ℝ → ℝ := fun r => 2 * r * √(h ^ 2 - r ^ 2 - 2 * p * r)
  have heq (r : ℝ) : h ^ 2 - r ^ 2 - 2 * p * r = q ^ 2 - (r + p) ^ 2 := by
    rw [hq2]
    ring
  have htail : (∫ r in Set.Ioi (0 : ℝ), f r) = ∫ r in Set.Ioc (0 : ℝ) b, f r := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun r hr => hr.1)
    intro r hr
    have hrb : b < r := lt_of_not_ge (fun hle => hr.2 ⟨hr.1, hle⟩)
    have hrq : q ≤ r + p := by dsimp [b] at hrb; linarith
    have hrq2 : q ^ 2 ≤ (r + p) ^ 2 := (sq_le_sq₀ hq.le (by linarith)).2 hrq
    have hn : h ^ 2 - r ^ 2 - 2 * p * r ≤ 0 := by rw [heq]; linarith
    simp [f, sqrt_eq_zero_of_nonpos hn]
  have hPc : Continuous (fun r : ℝ => P (r + p)) := by
    dsimp [P, s]
    fun_prop
  have hfc : Continuous f := by
    dsimp [f]
    fun_prop
  have hfinite : (∫ r in (0 : ℝ)..b, f r) = P q - P p := by
    calc
      (∫ r in (0 : ℝ)..b, f r) = P (b + p) - P (0 + p) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le
          hPc.continuousOn (f' := f) _ (hfc.intervalIntegrable 0 b)
        intro r hr
        have hr0 := hr.1
        have hrb := hr.2
        dsimp [b] at hrb
        have hd := (hder (r + p) (by linarith) (by linarith)).comp r
          ((hasDerivAt_id r).add_const p)
        convert! hd using 1
        dsimp [f, s]
        rw [heq]
        ring
      _ = P q - P p := by simp [b]
  have hs0 : s p = h := by
    dsimp [s]
    have he : q ^ 2 - p ^ 2 = h ^ 2 := by nlinarith [hq2]
    rw [he, sqrt_sq hh.le]
  have hpq : p / q ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hq).2
      linarith
    · apply (div_lt_iff₀ hq).2
      simpa using hp2
  have ha : arcsin (p / q) = arctan (p / h) := by
    rw [arcsin_eq_arctan hpq, hnorm p (by nlinarith [hq2]), hs0]
    congr 1
    field_simp
  have hsQ : s q = 0 := by simp [s]
  change (∫ r in Set.Ioi (0 : ℝ), f r) = _
  rw [htail, ← intervalIntegral.integral_of_le hb.le, hfinite]
  dsimp [P]
  rw [hsQ, hs0, div_self hq.ne', arcsin_one, ha, hq2]
  ring

private lemma F8a.radial_lintegral (h p : ℝ) (hh : 0 < h) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * r * √(h ^ 2 - r ^ 2 - 2 * p * r))) =
      ENNReal.ofReal (2 / 3 * h ^ 3 + p ^ 2 * h -
        p * (h ^ 2 + p ^ 2) * (π / 2 - arctan (p / h))) := by
  let f : ℝ → ℝ := fun r => 2 * r * √(h ^ 2 - r ^ 2 - 2 * p * r)
  let q := √(h ^ 2 + p ^ 2)
  let b := q - p
  have hq0 : 0 < q := sqrt_pos.2 (by nlinarith [sq_nonneg p])
  have hq2 : q ^ 2 = h ^ 2 + p ^ 2 := sq_sqrt (by positivity)
  have hb : 0 < b := by dsimp [b]; nlinarith [sq_pos_of_pos hh]
  have hf : Continuous f := by dsimp [f]; fun_prop
  have htail (r : ℝ) (hr : b < r) : f r = 0 := by
    have hsq : q ^ 2 ≤ (r + p) ^ 2 := by
      apply (sq_le_sq₀ hq0.le (by dsimp [b] at hr; linarith)).2
      dsimp [b] at hr
      linarith
    have hm : h ^ 2 - r ^ 2 - 2 * p * r ≤ 0 := by nlinarith [hq2]
    simp [f, sqrt_eq_zero_of_nonpos hm]
  have hi : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    have hfi : Integrable (Set.Icc (0 : ℝ) b |>.indicator f) volume :=
      (hf.integrableOn_Icc).integrable_indicator measurableSet_Icc
    apply hfi.integrableOn.congr_fun (s := Set.Ioi (0 : ℝ)) _ measurableSet_Ioi
    intro r hr
    by_cases hrb : r ≤ b
    · have hrmem : r ∈ Set.Icc (0 : ℝ) b := ⟨le_of_lt hr, hrb⟩
      simp only [Set.indicator_of_mem hrmem]
    · have hrmem : r ∉ Set.Icc (0 : ℝ) b := by simp [Set.mem_Icc, hrb]
      simp only [Set.indicator_of_notMem hrmem]
      exact (htail r (lt_of_not_ge hrb)).symm
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp [f]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hr)) (sqrt_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  congr 1
  exact F8a.f3 h p hh

private lemma cylinder_dist_sq (o : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (R ρ φ θ z : ℝ) :
    dist (o + (ρ*cos φ) • e 0 + (ρ*sin φ) • e 1 + z • e 2)
      (o - R • (cos θ • e 0 + sin θ • e 1)) ^ 2 =
      ρ^2 + R^2 + z^2 + 2*ρ*R*cos (φ-θ) := by
  have hsub :
      (o + (ρ*cos φ) • e 0 + (ρ*sin φ) • e 1 + z • e 2) -
          (o - R • (cos θ • e 0 + sin θ • e 1)) =
        (ρ*cos φ + R*cos θ) • e 0 +
          (ρ*sin φ + R*sin θ) • e 1 + z • e 2 := by
    simp only [smul_add, smul_smul, add_smul]
    abel
  have hinner := orthonormal_iff_ite.mp he
  rw [dist_eq_norm, hsub, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hinner]
  norm_num [Fin.ext_iff]
  rw [cos_sub]
  clear o e he hsub hinner
  linear_combination ρ^2 * sin_sq_add_cos_sq φ + R^2 * sin_sq_add_cos_sq θ

theorem proof_SolidGeom_volume_normal_form_angular
    (c : Fin 3 → E3) (o : E3) (e : Fin 3 → E3) (R ψ α₀ α₁ α₂ : ℝ)
    (he : Orthonormal ℝ e) (hR0 : 0 < R) (hR1 : R < 1)
    (h0 : 0 < α₀) (h1 : 0 < α₁) (h2 : 0 < α₂) (hs : α₀ + α₁ + α₂ = π)
    (hc0 : c 0 = o - R • (cos ψ • e 0 + sin ψ • e 1))
    (hc1 : c 1 = o - R • (cos (ψ + 2 * α₂) • e 0 + sin (ψ + 2 * α₂) • e 1))
    (hc2 : c 2 = o - R • (cos (ψ + 2 * α₂ + 2 * α₀) • e 0 +
      sin (ψ + 2 * α₂ + 2 * α₀) • e 1)) :
    let h := √(1 - R ^ 2)
    let I : ℝ → ℝ := fun p => 2 / 3 * h ^ 3 + p ^ 2 * h
      - p * (h ^ 2 + p ^ 2) * (π / 2 - arctan (p / h))
    (volume (Metric.closedBall (c 0) 1 ∩ Metric.closedBall (c 1) 1 ∩
      Metric.closedBall (c 2) 1)).toReal =
      ∫ φ in ψ..ψ + 2 * π,
        I (R * max (cos (φ - ψ)) (max (cos (φ - (ψ + 2 * α₂)))
          (cos (φ - (ψ + 2 * α₂ + 2 * α₀))))) := by
  classical
  dsimp only
  let h : ℝ := √(1 - R ^ 2)
  let I : ℝ → ℝ := fun p => 2 / 3 * h ^ 3 + p ^ 2 * h -
    p * (h ^ 2 + p ^ 2) * (π / 2 - arctan (p / h))
  let p : ℝ → ℝ := fun φ => R * max (cos (φ - ψ))
    (max (cos (φ - (ψ + 2 * α₂))) (cos (φ - (ψ + 2 * α₂ + 2 * α₀))))
  let S := Metric.closedBall (c 0) 1 ∩ Metric.closedBall (c 1) 1 ∩ Metric.closedBall (c 2) 1
  let X : ℝ → ℝ → ℝ → E3 := fun φ r z => o + (r * cos φ) • e 0 +
    (r * sin φ) • e 1 + z • e 2
  have hh : 0 < h := sqrt_pos.mpr (by nlinarith)
  have hh2 : h ^ 2 = 1 - R ^ 2 := sq_sqrt (by nlinarith)
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hmem (φ r z : ℝ) (hr : 0 ≤ r) :
      X φ r z ∈ S ↔ z ^ 2 ≤ h ^ 2 - r ^ 2 - 2 * p φ * r := by
    have hball (θ : ℝ) :
        dist (X φ r z) (o - R • (cos θ • e 0 + sin θ • e 1)) ≤ 1 ↔
          r ^ 2 + R ^ 2 + z ^ 2 + 2 * r * R * cos (φ - θ) ≤ 1 := by
      rw [← cylinder_dist_sq o e he R r φ θ z]
      simpa only [one_pow] using (sq_le_sq₀ (dist_nonneg :
        0 ≤ dist (X φ r z) (o - R • (cos θ • e 0 + sin θ • e 1))) zero_le_one).symm
    have hk : 0 ≤ 2 * r * R := mul_nonneg (mul_nonneg (by norm_num) hr) hR0.le
    have hm (a b : ℝ) :
        (r ^ 2 + R ^ 2 + z ^ 2 + 2 * r * R * a ≤ 1 ∧
          r ^ 2 + R ^ 2 + z ^ 2 + 2 * r * R * b ≤ 1) ↔
          r ^ 2 + R ^ 2 + z ^ 2 + 2 * r * R * max a b ≤ 1 := by
      by_cases hab : a ≤ b
      · rw [max_eq_right hab]
        constructor
        · exact And.right
        · intro hb
          exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hab hk], hb⟩
      · rw [max_eq_left (le_of_not_ge hab)]
        constructor
        · exact And.left
        · intro ha
          exact ⟨ha, by nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hab) hk]⟩
    dsimp only [S]
    simp only [Set.mem_inter_iff, Metric.mem_closedBall, hc0, hc1, hc2, hball]
    rw [and_assoc, hm, hm]
    dsimp only [p]
    rw [hh2]
    constructor <;> intro hm' <;> nlinarith
  have hz (φ r : ℝ) (hr : 0 < r) :
      (∫⁻ z : ℝ, ENNReal.ofReal r * S.indicator (fun _ : E3 => (1 : ENNReal)) (X φ r z)) =
        ENNReal.ofReal (2 * r * √(h ^ 2 - r ^ 2 - 2 * p φ * r)) := by
    let M := {z : ℝ | z ^ 2 ≤ h ^ 2 - r ^ 2 - 2 * p φ * r}
    have hM : MeasurableSet M := by dsimp [M]; measurability
    calc
      _ = ∫⁻ z : ℝ, ENNReal.ofReal r * M.indicator (fun _ => (1 : ENNReal)) z := by
        apply lintegral_congr
        intro z
        congr 1
        simp only [Set.indicator_apply, hmem φ r z hr.le]
        rfl
      _ = ENNReal.ofReal r * volume M := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_fun_one hM]
      _ = _ := by
        rw [F8a.f2]
        rw [← ENNReal.ofReal_mul hr.le]
        congr 1
        ring
  have hcyl := F8a.f1 o e he (S.indicator (fun _ : E3 => (1 : ENNReal)))
    (measurable_const.indicator hS)
  rw [lintegral_indicator_fun_one hS] at hcyl
  have hv : volume S = ∫⁻ φ in Set.Ioc (-π) π, ENNReal.ofReal (I (p φ)) := by
    rw [hcyl]
    apply lintegral_congr
    intro φ
    calc
      _ = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * r * √(h ^ 2 - r ^ 2 - 2 * p φ * r)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact hz φ r hr
      _ = _ := F8a.radial_lintegral h (p φ) hh
  have hnn : ∀ φ, 0 ≤ I (p φ) := by
    intro φ
    have heq := F8a.f3 h (p φ) hh
    have hn : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), 2 * r * √(h ^ 2 - r ^ 2 - 2 * p φ * r) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_nonneg (mul_nonneg (by norm_num) hr.le) (sqrt_nonneg _)
    dsimp [I]
    rw [← heq]
    exact hn
  have hcont : Continuous (fun φ => I (p φ)) := by
    dsimp [I, p]
    fun_prop
  have hper : Function.Periodic (fun φ => I (p φ)) (2 * π) := by
    intro φ
    dsimp [p]
    simp only [show ∀ θ : ℝ, φ + 2 * π - θ = (φ - θ) + 2 * π by intro θ; ring,
      cos_add_two_pi]
  calc
    _ = ∫ φ in Set.Ioc (-π) π, I (p φ) := by
      rw [hv, integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hnn) hcont.aestronglyMeasurable]
    _ = ∫ φ in (-π)..π, I (p φ) :=
      (intervalIntegral.integral_of_le (by linarith [pi_pos])).symm
    _ = _ := by
      simpa only [show -π + 2 * π = π by ring] using hper.intervalIntegral_add_eq (-π) ψ
