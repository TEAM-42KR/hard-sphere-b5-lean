import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
import HardSphereB5Lean.Definitions.Def_Gnomonic_inverseNorth
set_option autoImplicit false
noncomputable section
open MeasureTheory SphereGeom Gnomonic
private lemma p6geom_normSq2 (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

private lemma p6geom_normSq3 (u : E3) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  ring

private lemma p6geom_northRadius_pos (x : E2) : 0 < northRadius x := by
  unfold northRadius
  apply Real.sqrt_pos.2
  positivity

private lemma p6geom_northRadius_sq (x : E2) : northRadius x ^ 2 = 1 + ‖x‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

@[simp] private lemma northPlaneInclusion_zero (x : E2) : northPlaneInclusion x 0 = x 0 := by
  simp [northPlaneInclusion, EuclideanSpace.inner_single_left]
@[simp] private lemma northPlaneInclusion_one (x : E2) : northPlaneInclusion x 1 = x 1 := by
  simp [northPlaneInclusion, EuclideanSpace.inner_single_left]
@[simp] private lemma northPlaneInclusion_two (x : E2) : northPlaneInclusion x 2 = 0 := by
  simp [northPlaneInclusion, EuclideanSpace.inner_single_left]

@[simp] private lemma northLift_zero (x : E2) : northLift x 0 = x 0 := by simp [northLift,north]
@[simp] private lemma northLift_one (x : E2) : northLift x 1 = x 1 := by simp [northLift,north]
@[simp] private lemma northLift_two (x : E2) : northLift x 2 = 1 := by simp [northLift,north]

@[simp] private lemma inverseNorth_zero (x : E2) : inverseNorth x 0 = (northRadius x)⁻¹ * x 0 := by
  simp [inverseNorth]
@[simp] private lemma inverseNorth_one (x : E2) : inverseNorth x 1 = (northRadius x)⁻¹ * x 1 := by
  simp [inverseNorth]
@[simp] private lemma inverseNorth_two (x : E2) : inverseNorth x 2 = (northRadius x)⁻¹ := by
  simp [inverseNorth]

private lemma p6geom_northLift_norm (x : E2) : ‖northLift x‖ = northRadius x := by
  have hn : ‖northLift x‖ ^ 2 = northRadius x ^ 2 := by
    rw [p6geom_normSq3, p6geom_northRadius_sq, p6geom_normSq2]
    simp
    ring
  nlinarith [norm_nonneg (northLift x), (p6geom_northRadius_pos x)]

private theorem p6geom_inverseNorth_hemisphere (x : E2) :
    ‖inverseNorth x‖ = 1 ∧ 0 < inverseNorth x 2 := by
  constructor
  · rw [inverseNorth, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (p6geom_northRadius_pos x)),
      p6geom_northLift_norm, inv_mul_cancel₀ (p6geom_northRadius_pos x).ne']
  · rw [inverseNorth_two]
    exact inv_pos.mpr (p6geom_northRadius_pos x)

private theorem p6geom_projection_inverseNorth (x : E2) : projectionNorth (inverseNorth x) = x := by
  ext i
  fin_cases i <;> simp [projectionNorth, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm, (p6geom_northRadius_pos x).ne']

private lemma p6geom_hasFDerivAt_northRadius_inv (x : E2) :
    HasFDerivAt (fun y : E2 => (northRadius y)⁻¹)
      (-((northRadius x)^3)⁻¹ • innerSL ℝ x) x := by
  have hD : HasFDerivAt (fun y : E2 => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (1 : ℝ)
  have hR : HasFDerivAt northRadius
      ((1 / (2 * northRadius x)) • (2 • innerSL ℝ x)) x :=
    hD.sqrt (show 1 + ‖x‖ ^ 2 ≠ 0 by positivity)
  have hI := (hasDerivAt_inv (p6geom_northRadius_pos x).ne').comp_hasFDerivAt x hR
  apply hI.congr_fderiv
  ext h
  simp only [smul_apply, smul_eq_mul]
  field_simp [(p6geom_northRadius_pos x).ne']
  ring

private theorem p6geom_hasFDerivAt_inverseNorth (x : E2) :
    HasFDerivAt inverseNorth (inverseNorthDeriv x) x := by
  have hV : HasFDerivAt northLift northPlaneInclusion x :=
    northPlaneInclusion.hasFDerivAt.add_const north
  have h := (p6geom_hasFDerivAt_northRadius_inv x).smul hV
  apply h.congr_fderiv
  ext v i
  simp [inverseNorthDeriv, sub_eq_add_neg, smul_eq_mul, mul_assoc]

private theorem p6geom_fderiv_inverseNorth (x : E2) : fderiv ℝ inverseNorth x = inverseNorthDeriv x :=
  (p6geom_hasFDerivAt_inverseNorth x).fderiv

private lemma p6geom_inner_northPlaneInclusion (h k : E2) :
    inner ℝ (northPlaneInclusion h) (northPlaneInclusion k) = inner ℝ h k := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ]

private lemma p6geom_inner_northLift_inclusion (x h : E2) :
    inner ℝ (northLift x) (northPlaneInclusion h) = inner ℝ x h := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ]

private lemma p6geom_inner_inclusion_northLift (h x : E2) :
    inner ℝ (northPlaneInclusion h) (northLift x) = inner ℝ x h := by
  rw [real_inner_comm, p6geom_inner_northLift_inclusion]

private lemma p6geom_inner_northLift_self (x : E2) :
    inner ℝ (northLift x) (northLift x) = northRadius x ^ 2 := by
  rw [real_inner_self_eq_norm_sq, p6geom_northLift_norm]

private theorem p6geom_inner_inverseNorthDeriv (x h k : E2) :
    inner ℝ (inverseNorthDeriv x h) (inverseNorthDeriv x k) =
      inner ℝ h k / (1 + ‖x‖ ^ 2) -
        (inner ℝ x h * inner ℝ x k) / (1 + ‖x‖ ^ 2)^2 := by
  have hr := (p6geom_northRadius_pos x).ne'
  have he : inner ℝ (inverseNorthDeriv x h) (inverseNorthDeriv x k) =
      inner ℝ h k / (northRadius x)^2 -
        (inner ℝ x h * inner ℝ x k) / (northRadius x)^4 := by
    simp only [inverseNorthDeriv, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    simp only [map_inv₀, map_pow, RCLike.conj_to_real, p6geom_inner_northPlaneInclusion,
      p6geom_inner_northLift_inclusion, p6geom_inner_inclusion_northLift, p6geom_inner_northLift_self, innerSL_apply_apply]
    field_simp [hr]
    ring
  rw [he, p6geom_northRadius_sq, show (northRadius x)^4 = (1+‖x‖^2)^2 by
    rw [show (northRadius x)^4 = ((northRadius x)^2)^2 by ring, p6geom_northRadius_sq]]

private theorem p6geom_northGramMatrix_det (x : E2) :
    (northGramMatrix x).det = 1 / (1 + ‖x‖ ^ 2)^3 := by
  rw [Matrix.det_fin_two]
  simp only [northGramMatrix, p6geom_fderiv_inverseNorth, p6geom_inner_inverseNorthDeriv]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    p6geom_normSq2, div_eq_mul_inv]
  field_simp
  ring

private theorem p6geom_inverse_projectionNorth (u : E3) (hu : ‖u‖ = 1) (hu2 : 0 < u 2) :
    inverseNorth (projectionNorth u) = u := by
  have hn : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    rw [← p6geom_normSq3, hu]
    norm_num
  have hr2 : northRadius (projectionNorth u)^2 = ((u 2)⁻¹)^2 := by
    rw [p6geom_northRadius_sq, p6geom_normSq2]
    simp [projectionNorth]
    field_simp [hu2.ne']
    nlinarith [hn]
  have hr : northRadius (projectionNorth u) = (u 2)⁻¹ := by
    nlinarith [p6geom_northRadius_pos (projectionNorth u), inv_pos.mpr hu2]
  ext i
  fin_cases i
  · change inverseNorth (projectionNorth u) 0 = u 0
    rw [inverseNorth_zero, hr]
    simp [projectionNorth, div_eq_mul_inv, hu2.ne', mul_assoc, mul_left_comm, mul_comm]
  · change inverseNorth (projectionNorth u) 1 = u 1
    rw [inverseNorth_one, hr]
    simp [projectionNorth, div_eq_mul_inv, hu2.ne', mul_assoc, mul_left_comm, mul_comm]
  · change inverseNorth (projectionNorth u) 2 = u 2
    rw [inverseNorth_two, hr, inv_inv]

private def northContraction (x : E2) : E2 := (northRadius x)⁻¹ • x

private def northContractionDeriv (x : E2) : E2 →L[ℝ] E2 :=
  (northRadius x)⁻¹ • ContinuousLinearMap.id ℝ E2 -
    ((northRadius x)^3)⁻¹ • (innerSL ℝ x).smulRight x

@[simp] private theorem northContraction_zero (x : E2) : northContraction x 0 = inverseNorth x 0 := by
  simp [northContraction]
@[simp] private theorem northContraction_one (x : E2) : northContraction x 1 = inverseNorth x 1 := by
  simp [northContraction]

private theorem p6geom_hasFDerivAt_northContraction (x : E2) :
    HasFDerivAt northContraction (northContractionDeriv x) x := by
  have h := (p6geom_hasFDerivAt_northRadius_inv x).smul (hasFDerivAt_id x)
  apply h.congr_fderiv
  ext v i
  simp [northContractionDeriv, sub_eq_add_neg, smul_eq_mul, mul_assoc]

private theorem p6geom_fderiv_northContraction (x : E2) :
    fderiv ℝ northContraction x = northContractionDeriv x :=
  (p6geom_hasFDerivAt_northContraction x).fderiv

private theorem p6geom_det_fderiv_northContraction (x : E2) :
    (fderiv ℝ northContraction x).det = 1 / (1 + ‖x‖^2)^2 := by
  have hr := (p6geom_northRadius_pos x).ne'
  have hdet : (northContractionDeriv x).det =
      ((northRadius x)^2 - (x 0 ^ 2 + x 1 ^ 2)) / (northRadius x)^4 := by
    rw [ContinuousLinearMap.det,
      ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
      Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, northContractionDeriv,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right]
    field_simp [hr]
    ring
  have hnum : (northRadius x)^2 - (x 0 ^ 2 + x 1 ^ 2) = 1 := by
    rw [p6geom_northRadius_sq, p6geom_normSq2]
    ring
  rw [p6geom_fderiv_northContraction, hdet, hnum,
    show (northRadius x)^4 = (1+‖x‖^2)^2 by
      rw [show (northRadius x)^4 = ((northRadius x)^2)^2 by ring, p6geom_northRadius_sq]]

private lemma p6geom_inv_radius_cube_eq_rpow (x : E2) :
    ((northRadius x)^3)⁻¹ = (1 + ‖x‖^2) ^ ((-3 : ℝ)/2) := by
  symm
  rw [show (-3 : ℝ)/2 = -((1/2 : ℝ)*(3 : ℝ)) by norm_num,
    Real.rpow_neg (show 0 ≤ 1+‖x‖^2 by positivity),
    Real.rpow_mul (show 0 ≤ 1+‖x‖^2 by positivity),
    ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_ofNat, northRadius]

private theorem p6geom_northContraction_det_div_height (x : E2) :
    (fderiv ℝ northContraction x).det / inverseNorth x 2 =
      (1 + ‖x‖^2) ^ ((-3 : ℝ)/2) := by
  rw [p6geom_det_fderiv_northContraction, inverseNorth_two, ← p6geom_inv_radius_cube_eq_rpow,
    ← p6geom_northRadius_sq]
  field_simp [(p6geom_northRadius_pos x).ne']

private def northSurfaceDensity (x : E2) : ℝ := Real.sqrt (northGramMatrix x).det

private theorem p6geom_northSurfaceDensity_eq (x : E2) :
    northSurfaceDensity x = (1 + ‖x‖^2) ^ ((-3 : ℝ)/2) := by
  have he : (northGramMatrix x).det = (((northRadius x)^3)⁻¹)^2 := by
    rw [p6geom_northGramMatrix_det, inv_pow,
      show ((northRadius x)^3)^2 = ((northRadius x)^2)^3 by ring, p6geom_northRadius_sq]
    simp
  rw [northSurfaceDensity, he, Real.sqrt_sq_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos (p6geom_northRadius_pos x) 3)), p6geom_inv_radius_cube_eq_rpow]

private lemma frame_inverse_eq (R : E3 ≃ₗᵢ[ℝ] E3) (x : Plane) :
    inverseFrame R x = R (inverseNorth x) := by
  have hl : WithLp.toLp 2 ![x 0,x 1,1] = northLift x := by
    ext i
    fin_cases i <;> simp [northLift_zero,northLift_one,northLift_two]
  simp only [inverseFrame,inverseNorth,northRadius,hl]

theorem proof_Gnomonic_frameChartInverse (R : E3 ≃ₗᵢ[ℝ] E3) :
  Measurable (inverseFrame R) ∧
  (∀ u ∈ hemisphereFrame R, inverseFrame R (chartFrame R u) = u) ∧
  (∀ x, chartFrame R (inverseFrame R x) = x) := by
  have hi : Continuous inverseNorth := continuous_iff_continuousAt.mpr
    (fun x => (p6geom_hasFDerivAt_inverseNorth x).continuousAt)
  have hfe : inverseFrame R = fun x => R (inverseNorth x) := funext (frame_inverse_eq R)
  refine ⟨?_,?_,?_⟩
  · rw [hfe]; exact (R.continuous.comp hi).measurable
  · intro u hu
    rw [frame_inverse_eq]
    change R (inverseNorth (projectionNorth (R.symm u))) = u
    rw [p6geom_inverse_projectionNorth (R.symm u)
      (by simpa only [R.symm.norm_map] using hu.1) hu.2]
    exact R.apply_symm_apply u
  · intro x
    rw [frame_inverse_eq]
    change projectionNorth (R.symm (R (inverseNorth x))) = x
    rw [R.symm_apply_apply]
    exact p6geom_projection_inverseNorth x
