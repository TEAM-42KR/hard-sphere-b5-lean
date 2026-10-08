import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000

private theorem heightChange :
    ((volume : Measure ℝ).restrict (Set.Ioo (1/2) 1)) =
      (1/2 : ℝ≥0∞) • ((volume.restrict (Set.Ioo (0 : ℝ) 1)).map (fun x => 1-x/2)) := by
  let k : ℝ → ℝ := fun x => 1-x/2
  have hk : Measurable k := by unfold k; fun_prop
  have hi : k '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (1/2 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor <;> dsimp [k] <;> linarith [hx.1, hx.2]
    · intro hz
      refine ⟨2-2*z, ?_, ?_⟩
      · constructor <;> linarith [hz.1, hz.2]
      · unfold k; ring
  have hj : Set.InjOn k (Set.Ioo (0 : ℝ) 1) := by
    intro x hx y hy h; dsimp [k] at h; linarith
  have hd (x : ℝ) (_hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivWithinAt k (-1/2) (Set.Ioo (0 : ℝ) 1) x := by
    have h : HasDerivAt k (-1/2) x := by
      rw [show (-1 : ℝ)/2 = 0-1/2 by ring]
      exact (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).div_const (2 : ℝ))
    exact h.hasDerivWithinAt
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_smul_measure, lintegral_map hg hk]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hj g
  rw [hi] at h
  rw [h]
  rw [abs_of_neg (by norm_num : (-1 : ℝ)/2 < 0)]
  simp only [neg_div, neg_neg]
  rw [lintegral_const_mul'' _
    (show AEMeasurable (fun x => g (k x)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) from
      (hg.comp hk).aemeasurable)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
  norm_num

private theorem chart_norm_sq (a b c : ℝ) :
    ‖a • e1 + b • e2 + c • e‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, e, e1, e2, Fin.sum_univ_succ]
  ring

private theorem frameA : Orthonormal ℝ ![e1, e2, e] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e1, e2, e, EuclideanSpace.inner_single_left]

private theorem frameB : Orthonormal ℝ ![e1, e2, -e] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e1, e2, e, EuclideanSpace.inner_single_left]

private theorem sphereMeasure_translate (c : Pt) :
    sphereMeasure c = dOmega.map (fun u => c+u) := by
  unfold dOmega sphereMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, zero_add]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_endpointCylinderMeasures :
    ((sphereMeasure 0).restrict FA =
      (1 / 2 : ℝ≥0∞) • (((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))).map
        (fun x : ℝ × ℝ =>
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.cos x.2) • e1 +
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.sin x.2) • e2 + (1 - x.1 / 2) • e)) ∧
    ((sphereMeasure e).restrict FB =
      (1 / 2 : ℝ≥0∞) • (((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))).map
        (fun x : ℝ × ℝ =>
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.cos x.2) • e1 +
          (Real.sqrt (x.1 * (1 - x.1 / 4)) * Real.sin x.2) • e2 + (x.1 / 2) • e))  := by
  let r : ℝ → ℝ := fun z => Real.sqrt (1-z^2)
  let CA : ℝ × ℝ → Pt := fun p =>
    (r p.1 * Real.cos p.2) • e1 + (r p.1 * Real.sin p.2) • e2 + p.1 • e
  let CB : ℝ × ℝ → Pt := fun p =>
    (r p.1 * Real.cos p.2) • e1 + (r p.1 * Real.sin p.2) • e2 + (1-p.1) • e
  let S : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2*Real.pi)
  let Z : Set (ℝ × ℝ) := Set.Icc (1/2 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2*Real.pi)
  have hCA : Measurable CA := by unfold CA r; fun_prop
  have hCB : Measurable CB := by unfold CB r; fun_prop
  have hrad (p : ℝ × ℝ) (hp : p ∈ S) : 0 ≤ 1-p.1^2 := by
    have h1 : 0 ≤ 1-p.1 := by linarith [hp.1.2]
    have h2 : 0 ≤ 1+p.1 := by linarith [hp.1.1]
    nlinarith [mul_nonneg h1 h2]
  have hcirc (p : ℝ × ℝ) (hp : p ∈ S) :
      (r p.1 * Real.cos p.2)^2 + (r p.1 * Real.sin p.2)^2 = 1-p.1^2 := by
    simp only [mul_pow, r, Real.sq_sqrt (hrad p hp)]
    nlinarith [congrArg (fun t : ℝ => (1-p.1^2)*t) (Real.sin_sq_add_cos_sq p.2)]
  have hdistA (p : ℝ × ℝ) (hp : p ∈ S) :
      ‖CA p‖^2 = 1 ∧ ‖CA p-e‖^2 = 2-2*p.1 := by
    constructor
    · unfold CA
      rw [chart_norm_sq]
      nlinarith [hcirc p hp]
    · have h : CA p-e = (r p.1 * Real.cos p.2) • e1 +
          (r p.1 * Real.sin p.2) • e2 + (p.1-1) • e := by unfold CA; module
      rw [h, chart_norm_sq]
      nlinarith [hcirc p hp]
  have hdistB (p : ℝ × ℝ) (hp : p ∈ S) :
      ‖CB p-e‖^2 = 1 ∧ ‖CB p‖^2 = 2-2*p.1 := by
    constructor
    · have h : CB p-e = (r p.1 * Real.cos p.2) • e1 +
          (r p.1 * Real.sin p.2) • e2 + (-p.1) • e := by unfold CB; module
      rw [h, chart_norm_sq]
      nlinarith [hcirc p hp]
    · unfold CB
      rw [chart_norm_sq]
      nlinarith [hcirc p hp]
  have hpreA : CA ⁻¹' FA ∩ S = Z := by
    ext p
    constructor
    · rintro ⟨hpFA, hpS⟩
      have hnorm : ‖CA p-e‖ ≤ 1 := by simpa [FA, Metric.mem_closedBall, dist_eq_norm] using hpFA.2
      have hsq : ‖CA p-e‖^2 ≤ 1 := by nlinarith [norm_nonneg (CA p-e)]
      exact ⟨⟨by nlinarith [(hdistA p hpS).2], hpS.1.2⟩, hpS.2⟩
    · intro hpZ
      have hpS : p ∈ S := ⟨⟨by linarith [hpZ.1.1], hpZ.1.2⟩, hpZ.2⟩
      refine ⟨?_, hpS⟩
      constructor
      · change dist (CA p) 0 = 1
        rw [dist_zero_right]
        nlinarith [(hdistA p hpS).1, norm_nonneg (CA p)]
      · change dist (CA p) e ≤ 1
        rw [dist_eq_norm]
        nlinarith [(hdistA p hpS).2, norm_nonneg (CA p-e), hpZ.1.1]
  have hpreB : CB ⁻¹' FB ∩ S = Z := by
    ext p
    constructor
    · rintro ⟨hpFB, hpS⟩
      have hnorm : ‖CB p‖ ≤ 1 := by simpa [FB, Metric.mem_closedBall, dist_zero_right] using hpFB.2
      have hsq : ‖CB p‖^2 ≤ 1 := by nlinarith [norm_nonneg (CB p)]
      exact ⟨⟨by nlinarith [(hdistB p hpS).2], hpS.1.2⟩, hpS.2⟩
    · intro hpZ
      have hpS : p ∈ S := ⟨⟨by linarith [hpZ.1.1], hpZ.1.2⟩, hpZ.2⟩
      refine ⟨?_, hpS⟩
      constructor
      · change dist (CB p) e = 1
        rw [dist_eq_norm]
        nlinarith [(hdistB p hpS).1, norm_nonneg (CB p-e)]
      · change dist (CB p) 0 ≤ 1
        rw [dist_zero_right]
        nlinarith [(hdistB p hpS).2, norm_nonneg (CB p), hpZ.1.1]
  have hmapA : sphereMeasure 0 = (volume.restrict S).map CA := by
    have h := SphereGeom.dOmega_map_cylinder ![e1, e2, e] frameA
    simpa [dOmega, CA, r, S] using h
  have hmapB : sphereMeasure e = (volume.restrict S).map CB := by
    rw [sphereMeasure_translate, SphereGeom.dOmega_map_cylinder ![e1,e2,-e] frameB,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    dsimp [CB, r, S]
    module
  have hFA : MeasurableSet FA := (Metric.isClosed_sphere.inter Metric.isClosed_closedBall).measurableSet
  have hFB : MeasurableSet FB := (Metric.isClosed_sphere.inter Metric.isClosed_closedBall).measurableSet
  have hrestrictedA : (sphereMeasure 0).restrict FA = (volume.restrict Z).map CA := by
    rw [hmapA, Measure.restrict_map hCA hFA,
      Measure.restrict_restrict (hFA.preimage hCA), hpreA]
  have hrestrictedB : (sphereMeasure e).restrict FB = (volume.restrict Z).map CB := by
    rw [hmapB, Measure.restrict_map hCB hFB,
      Measure.restrict_restrict (hFB.preimage hCB), hpreB]
  let μX : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let μφ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2*Real.pi))
  let T : ℝ × ℝ → ℝ × ℝ := Prod.map (fun x : ℝ => 1-x/2) id
  have hT : Measurable T := by unfold T; fun_prop
  have hZmap : (volume : Measure (ℝ × ℝ)).restrict Z = (1/2 : ℝ≥0∞) • (μX.prod μφ).map T := by
    unfold Z
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
    rw [← Measure.prod_restrict, ← restrict_Ioo_eq_restrict_Icc,
      restrict_Ico_eq_restrict_Ioc, heightChange, Measure.prod_smul_left]
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id]
    simp only [Measure.map_id]
    rfl
  have hae : ∀ᵐ p ∂μX.prod μφ, 0 < p.1 ∧ p.1 < 1 := by
    rw [Measure.prod_restrict]
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact hp.1
  have hsqrt (X : ℝ) : r (1-X/2) = Real.sqrt (X*(1-X/4)) := by
    unfold r
    congr 1
    ring
  constructor
  · rw [hrestrictedA, hZmap, Measure.map_smul, Measure.map_map hCA hT]
    congr 1
    apply Measure.map_congr
    filter_upwards [hae] with p hp
    simp [Function.comp_apply, CA, T, Prod.map_apply, id_eq, hsqrt]
  · rw [hrestrictedB, hZmap, Measure.map_smul, Measure.map_map hCB hT]
    congr 1
    apply Measure.map_congr
    filter_upwards [hae] with p hp
    simp [Function.comp_apply, CB, T, Prod.map_apply, id_eq, hsqrt]
