import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_endpointCylinderMeasures
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_existsAxialRotation
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_parameterizedCommonAngleAveraging
set_option autoImplicit false

open MeasureTheory Set SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped ENNReal

set_option maxHeartbeats 1500000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_angularEndpointReduction (K : Pt → Pt → ℝ)
    (hint : Integrable (Function.uncurry K)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)))
    (hrot : ∀ R, IsAxialRotation R → ∀ p ∈ FA, ∀ p' ∈ FB, K (R p) (R p') = K p p') :
    Integrable (fun v : (ℝ × ℝ) × ℝ => K (pRep v.1.1) (pRep2 v.1.2 v.2))
      (((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) 1))).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) ∧
    (∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0)) =
      Real.pi / 2 * ∫ v : (ℝ × ℝ) × ℝ, K (pRep v.1.1) (pRep2 v.1.2 v.2)
        ∂(((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) 1))).prod
            (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
  classical
  let ν : Measure ℝ := volume.restrict (Ioo 0 1)
  let μφ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let η : Measure (ℝ × ℝ) := ν.prod ν
  let κ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  let D : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1
  let A : ℝ × ℝ → Pt := fun p =>
    (Real.sqrt (p.1 * (1 - p.1 / 4)) * Real.cos p.2) • e1 +
    (Real.sqrt (p.1 * (1 - p.1 / 4)) * Real.sin p.2) • e2 + (1 - p.1 / 2) • e
  let B : ℝ × ℝ → Pt := fun p =>
    (Real.sqrt (p.1 * (1 - p.1 / 4)) * Real.cos p.2) • e1 +
    (Real.sqrt (p.1 * (1 - p.1 / 4)) * Real.sin p.2) • e2 + (p.1 / 2) • e
  have hA : Measurable A := by unfold A; fun_prop
  have hB : Measurable B := by unfold B; fun_prop
  let F : (ℝ × ℝ) × (ℝ × ℝ) → Pt × Pt := Prod.map A B
  have hF : Measurable F := hA.prodMap hB
  have hEA : (sphereMeasure 0).restrict FA = (1 / 2 : ℝ≥0∞) • (ν.prod μφ).map A :=
    HardSphereB5.SphericalCrofton.Aux.Flat.endpointCylinderMeasures.1
  have hEB : (sphereMeasure e).restrict FB = (1 / 2 : ℝ≥0∞) • (ν.prod μφ).map B :=
    HardSphereB5.SphericalCrofton.Aux.Flat.endpointCylinderMeasures.2
  letI : SFinite ((sphereMeasure 0).restrict FA) := by rw [hEA]; infer_instance
  letI : SFinite ((sphereMeasure e).restrict FB) := by rw [hEB]; infer_instance
  have hEP : ((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB) =
      (1 / 4 : ℝ≥0∞) • (((ν.prod μφ).prod (ν.prod μφ)).map F) := by
    rw [hEA, hEB, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_prod_map _ _ hA hB]
    simp only [one_div]
    rw [← ENNReal.mul_inv (by left; norm_num : (2 : ℝ≥0∞) ≠ 0 ∨ (2 : ℝ≥0∞) ≠ ∞)
      (by left; norm_num : (2 : ℝ≥0∞) ≠ ∞ ∨ (2 : ℝ≥0∞) ≠ 0)]
    norm_num [F]
  have hmap : Integrable (Function.uncurry K) (((ν.prod μφ).prod (ν.prod μφ)).map F) := by
    have h := hint
    rw [hEP] at h
    exact (integrable_smul_measure (by norm_num : (1 / 4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ∞)).mp h
  let W : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => K (A p.1) (B p.2)
  have hW : Integrable W ((ν.prod μφ).prod (ν.prod μφ)) :=
    hmap.comp_measurable hF
  have hendpoint :
      (∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0)) =
        (1 / 4 : ℝ) * ∫ p, W p ∂((ν.prod μφ).prod (ν.prod μφ)) := by
    rw [MeasureTheory.integral_integral hint, hEP, integral_smul_measure,
      integral_map (f := fun p : Pt × Pt => K p.1 p.2)
        hF.aemeasurable hmap.aestronglyMeasurable]
    norm_num [F, W, Function.uncurry, Prod.map_apply]
  let E : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ᵐ ((ℝ × ℝ) × (ℝ × ℝ)) :=
    { toEquiv := Equiv.prodProdProdComm ℝ ℝ ℝ ℝ
      measurable_toFun := by
        change Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
        fun_prop
      measurable_invFun := by
        change Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
        fun_prop }
  have hmid : MeasurePreserving
      (fun p : ℝ × (ℝ × ℝ) => (p.2.1, (p.1, p.2.2)))
      (ν.prod (μφ.prod μφ)) (μφ.prod (ν.prod μφ)) := by
    exact (measurePreserving_prodAssoc μφ ν μφ).comp
      (((Measure.measurePreserving_swap (μ := ν) (ν := μφ)).prod
        (MeasurePreserving.id μφ)).comp
          (MeasurePreserving.symm MeasurableEquiv.prodAssoc
            (measurePreserving_prodAssoc ν μφ μφ)))
  have hE : MeasurePreserving E (η.prod (μφ.prod μφ)) ((ν.prod μφ).prod (ν.prod μφ)) := by
    exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ν μφ (ν.prod μφ))).comp
      (((MeasurePreserving.id ν).prod hmid).comp
        (measurePreserving_prodAssoc ν ν (μφ.prod μφ)))
  let V : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p =>
    K (A (p.1.1, p.2.1)) (B (p.1.2, p.2.2))
  have hV : Integrable V (η.prod (μφ.prod μφ)) :=
    hE.integrable_comp_of_integrable hW
  have hWV : (∫ p, W p ∂((ν.prod μφ).prod (ν.prod μφ))) =
      ∫ p, V p ∂(η.prod (μφ.prod μφ)) :=
    (hE.integral_comp E.measurableEmbedding W).symm
  have hdom : ∀ᵐ x ∂η, x ∈ D := by
    dsimp [η, ν, D]
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)
  let Q : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => if p.1 ∈ D then V p else 0
  have hQV : Q =ᵐ[η.prod (μφ.prod μφ)] V := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hdom] with p hp
    simp only [Q, if_pos hp]
  have hQ : Integrable Q (η.prod (μφ.prod μφ)) := hV.congr hQV.symm
  have hn (a b c : ℝ) : ‖a • e1 + b • e2 + c • e‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, e, e1, e2, Fin.sum_univ_succ]
    ring
  have hcircle (X a : ℝ) (hX : X ∈ Ioo (0 : ℝ) 1) :
      (Real.sqrt (X * (1 - X / 4)) * Real.cos a)^2 +
      (Real.sqrt (X * (1 - X / 4)) * Real.sin a)^2 = X * (1 - X / 4) := by
    have hr : 0 ≤ X * (1 - X / 4) := mul_nonneg hX.1.le (by linarith [hX.2])
    simp only [mul_pow, Real.sq_sqrt hr]
    nlinarith [congrArg (fun z : ℝ => (X * (1 - X / 4)) * z) (Real.sin_sq_add_cos_sq a)]
  have hAmem (X a : ℝ) (hX : X ∈ Ioo (0 : ℝ) 1) : A (X, a) ∈ FA := by
    have hs : ‖A (X, a)‖^2 = 1 := by
      dsimp [A]
      rw [hn]
      nlinarith [hcircle X a hX]
    have hd : ‖A (X, a) - e‖^2 = X := by
      have heq : A (X, a) - e =
          (Real.sqrt (X * (1 - X / 4)) * Real.cos a) • e1 +
          (Real.sqrt (X * (1 - X / 4)) * Real.sin a) • e2 + (-X / 2) • e := by
        dsimp [A]
        module
      rw [heq, hn]
      nlinarith [hcircle X a hX]
    constructor
    · change dist (A (X, a)) 0 = 1
      rw [dist_zero_right]
      nlinarith [norm_nonneg (A (X, a))]
    · change dist (A (X, a)) e ≤ 1
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (A (X, a) - e), hX.2]
  have hBmem (Y b : ℝ) (hY : Y ∈ Ioo (0 : ℝ) 1) : B (Y, b) ∈ FB := by
    have hd : ‖B (Y, b) - e‖^2 = 1 := by
      have heq : B (Y, b) - e =
          (Real.sqrt (Y * (1 - Y / 4)) * Real.cos b) • e1 +
          (Real.sqrt (Y * (1 - Y / 4)) * Real.sin b) • e2 + (Y / 2 - 1) • e := by
        dsimp [B]
        module
      rw [heq, hn]
      nlinarith [hcircle Y b hY]
    have hs : ‖B (Y, b)‖^2 = Y := by
      dsimp [B]
      rw [hn]
      nlinarith [hcircle Y b hY]
    constructor
    · change dist (B (Y, b)) e = 1
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (B (Y, b) - e)]
    · change dist (B (Y, b)) 0 ≤ 1
      rw [dist_zero_right]
      nlinarith [norm_nonneg (B (Y, b)), hY.2]
  have hper (x : ℝ × ℝ) : Function.Periodic (fun χ : ℝ => Q (x, (0, χ))) (2 * Real.pi) := by
    intro χ
    dsimp [Q, V, B]
    simp only [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hdiag (x : ℝ × ℝ) (a b t : ℝ) : Q (x, (a + t, b + t)) = Q (x, (a, b)) := by
    by_cases hx : x ∈ D
    · simp only [Q, if_pos hx, V]
      obtain ⟨R, hR, hc⟩ := HardSphereB5.SphericalCrofton.Aux.Flat.existsAxialRotation t
      have hRA : R (A (x.1, a)) = A (x.1, a + t) := by
        dsimp [A]
        rw [hc]
        congr 2 <;> simp only [Real.cos_add, Real.sin_add] <;> ring
      have hRB : R (B (x.2, b)) = B (x.2, b + t) := by
        dsimp [B]
        rw [hc]
        congr 2 <;> simp only [Real.cos_add, Real.sin_add] <;> ring
      rw [← hRA, ← hRB]
      exact hrot R hR _ (hAmem x.1 a hx.1) _ (hBmem x.2 b hx.2)
    · simp only [Q, if_neg hx]
  have hav := HardSphereB5.SphericalCrofton.Aux.Flat.parameterizedCommonAngleAveraging η
    (2 * Real.pi) (by positivity) Q hQ hper hdiag
  have hκ : volume.restrict (Ioc (-(2 * Real.pi / 2)) (2 * Real.pi / 2)) = κ := by
    rw [show (2 * Real.pi / 2 : ℝ) = Real.pi by ring]
    exact restrict_Ioo_eq_restrict_Ioc.symm
  rw [hκ] at hav
  let q : (ℝ × ℝ) × ℝ → ℝ := fun v => K (pRep v.1.1) (pRep2 v.1.2 v.2)
  have hqeq : (fun p : (ℝ × ℝ) × ℝ => Q (p.1, (0, p.2))) =ᵐ[η.prod κ] q := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hdom] with p hp
    simp [Q, V, A, B, q, pRep, pRep2, hp]
  refine ⟨hav.1.congr hqeq, ?_⟩
  calc
    (∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0)) =
        (1 / 4 : ℝ) * ∫ p, V p ∂(η.prod (μφ.prod μφ)) := by rw [hendpoint, hWV]
    _ = (1 / 4 : ℝ) * ∫ p, Q p ∂(η.prod (μφ.prod μφ)) := by
      rw [integral_congr_ae hQV]
    _ = (1 / 4 : ℝ) * ((2 * Real.pi) * ∫ p, q p ∂(η.prod κ)) := by
      rw [hav.2, integral_congr_ae hqeq]
    _ = Real.pi / 2 * ∫ p, q p ∂(η.prod κ) := by ring
