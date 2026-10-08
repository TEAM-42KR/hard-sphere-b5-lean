import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_flat_measure_general
set_option autoImplicit false

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
private theorem W4_coord_norm_sq (a b c : ℝ) :
    ‖a • e + b • e1 + c • e2‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, e, e1, e2, Fin.sum_univ_succ, add_assoc]

private theorem W4_coord_norm_le_one (v : Pt) (hv : ‖v‖ ^ 2 ≤ 1) : ‖v‖ ≤ 1 := by
  nlinarith [norm_nonneg v]

private theorem W4_pRep_mem_FA (X : ℝ) (hX0 : 0 < X) (hX1 : X < 1) : pRep X ∈ FA := by
  have hfactor : 0 ≤ 1 - X / 4 := by linarith
  have hr : 0 ≤ X * (1 - X / 4) := mul_nonneg hX0.le hfactor
  have hr2 := Real.sq_sqrt hr
  have hn : ‖pRep X‖ ^ 2 = 1 := by
    unfold pRep
    rw [add_comm]
    have h := W4_coord_norm_sq (1 - X / 2) (√(X * (1 - X / 4))) 0
    simp only [zero_smul, add_zero] at h
    rw [h, hr2]
    ring
  have hd : ‖pRep X - e‖ ^ 2 = X := by
    have hv : pRep X - e = (-X / 2) • e + √(X * (1 - X / 4)) • e1 + (0 : ℝ) • e2 := by
      unfold pRep
      module
    rw [hv]
    rw [W4_coord_norm_sq (-X / 2) (√(X * (1 - X / 4))) 0, hr2]
    ring
  constructor
  · change dist (pRep X) 0 = 1
    rw [dist_zero_right]
    nlinarith [norm_nonneg (pRep X)]
  · change dist (pRep X) e ≤ 1
    rw [dist_eq_norm]
    exact W4_coord_norm_le_one _ (by rw [hd]; exact hX1.le)

private theorem W4_pRep2_mem_FB (Y χ : ℝ) (hY0 : 0 < Y) (hY1 : Y < 1) : pRep2 Y χ ∈ FB := by
  have hfactor : 0 ≤ 1 - Y / 4 := by linarith
  have hr : 0 ≤ Y * (1 - Y / 4) := mul_nonneg hY0.le hfactor
  have hr2 := Real.sq_sqrt hr
  have htrig := Real.sin_sq_add_cos_sq χ
  have hcirc : (√(Y * (1 - Y / 4)) * Real.cos χ) ^ 2 +
      (√(Y * (1 - Y / 4)) * Real.sin χ) ^ 2 = Y * (1 - Y / 4) := by
    rw [mul_pow, mul_pow, hr2]
    nlinarith [congrArg (fun t : ℝ => Y * (1 - Y / 4) * t) htrig]
  have hn : ‖pRep2 Y χ - e‖ ^ 2 = 1 := by
    have hv : pRep2 Y χ - e = (Y / 2 - 1) • e +
        (√(Y * (1 - Y / 4)) * Real.cos χ) • e1 +
        (√(Y * (1 - Y / 4)) * Real.sin χ) • e2 := by
      unfold pRep2
      module
    rw [hv, W4_coord_norm_sq]
    nlinarith [hcirc]
  have hd : ‖pRep2 Y χ‖ ^ 2 = Y := by
    have hv : pRep2 Y χ = (Y / 2) • e +
        (√(Y * (1 - Y / 4)) * Real.cos χ) • e1 +
        (√(Y * (1 - Y / 4)) * Real.sin χ) • e2 := by
      unfold pRep2
      abel
    rw [hv, W4_coord_norm_sq]
    nlinarith [hcirc]
  constructor
  · change dist (pRep2 Y χ) e = 1
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (pRep2 Y χ - e)]
  · change dist (pRep2 Y χ) 0 ≤ 1
    rw [dist_zero_right]
    exact W4_coord_norm_le_one _ (by rw [hd]; exact hY1.le)

private def W4_reflectSheet : Pt ≃ₗᵢ[ℝ] Pt := (ℝ ∙ e2)ᗮ.reflection

private theorem W4_reflectSheet_e : W4_reflectSheet e = e := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [e2, e, EuclideanSpace.inner_single_left]

private theorem W4_reflectSheet_e1 : W4_reflectSheet e1 = e1 := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [e2, e1, EuclideanSpace.inner_single_left]

private theorem W4_reflectSheet_e2 : W4_reflectSheet e2 = -e2 :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg e2

private theorem W4_reflectSheet_pRep (X : ℝ) : W4_reflectSheet (pRep X) = pRep X := by
  simp only [pRep, map_add, map_smul, W4_reflectSheet_e1, W4_reflectSheet_e]

private theorem W4_reflectSheet_pRep2 (Y χ : ℝ) : W4_reflectSheet (pRep2 Y χ) = pRep2 Y (-χ) := by
  simp only [pRep2, map_add, map_smul, W4_reflectSheet_e1, W4_reflectSheet_e2, W4_reflectSheet_e,
    Real.cos_neg, Real.sin_neg, mul_neg, neg_smul, smul_neg]

theorem proof_HardSphereB5_SphericalCrofton_flat_measure_reflection_even (K : Pt → Pt → ℝ)
    (hint : Integrable (Function.uncurry K)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)))
    (hinv : ∀ R : Pt ≃ₗᵢ[ℝ] Pt, R e = e → ∀ p ∈ FA, ∀ p' ∈ FB, K (R p) (R p') = K p p') :
    ∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0) =
      π * ∫ v in Dfull,
        K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) / √(Hpoly v.1 v.2.1 v.2.2) := by
  rw [HardSphereB5.SphericalCrofton.flat_measure_general K hint (fun R hR => hinv R hR.1)]
  have hsheet (v : ℝ × ℝ × ℝ) (hv : v ∈ Dfull) :
      K (pRep v.1) (pRep2 v.2.1 (-chiPlus v.1 v.2.1 v.2.2)) =
      K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) := by
    have h := hinv W4_reflectSheet W4_reflectSheet_e
      (pRep v.1) (W4_pRep_mem_FA v.1 hv.1 hv.2.1)
      (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2))
      (W4_pRep2_mem_FB v.2.1 _ hv.2.2.1 hv.2.2.2.1)
    simpa only [W4_reflectSheet_pRep, W4_reflectSheet_pRep2] using h
  have hfold :
      (∫ v in Dfull,
        (K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) +
            K (pRep v.1) (pRep2 v.2.1 (-chiPlus v.1 v.2.1 v.2.2))) / √(Hpoly v.1 v.2.1 v.2.2)) =
      2 * ∫ v in Dfull,
        K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) / √(Hpoly v.1 v.2.1 v.2.2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun
    · unfold Dfull Hpoly
      measurability
    · intro v hv
      dsimp only
      rw [hsheet v hv]
      ring
  rw [hfold]
  ring
