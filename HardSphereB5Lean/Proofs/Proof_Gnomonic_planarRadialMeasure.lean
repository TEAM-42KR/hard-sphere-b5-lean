import Mathlib
import HardSphereB5Lean.Definitions.Def_Gnomonic_unitDisk
import HardSphereB5Lean.Definitions.Def_Gnomonic_inverseNorth
set_option autoImplicit false

noncomputable section
open MeasureTheory SphereGeom Gnomonic
open scoped ENNReal RealInnerProductSpace

private lemma p6rad_normSq2 (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

private lemma p6rad_northRadius_pos (x : E2) : 0 < northRadius x := by
  unfold northRadius
  apply Real.sqrt_pos.2
  positivity

private lemma p6rad_northRadius_sq (x : E2) : northRadius x ^ 2 = 1 + ‖x‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

private lemma p6rad_hasFDerivAt_northRadius_inv (x : E2) :
    HasFDerivAt (fun y : E2 => (northRadius y)⁻¹)
      (-((northRadius x)^3)⁻¹ • innerSL ℝ x) x := by
  have hD : HasFDerivAt (fun y : E2 => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (1 : ℝ)
  have hR : HasFDerivAt northRadius
      ((1 / (2 * northRadius x)) • (2 • innerSL ℝ x)) x :=
    hD.sqrt (show 1 + ‖x‖ ^ 2 ≠ 0 by positivity)
  have hI := (hasDerivAt_inv (p6rad_northRadius_pos x).ne').comp_hasFDerivAt x hR
  apply hI.congr_fderiv
  ext h
  simp only [smul_apply, smul_eq_mul]
  field_simp [(p6rad_northRadius_pos x).ne']
  ring

private def p6rad_northContraction (x : E2) : E2 := (northRadius x)⁻¹ • x

private def p6rad_northContractionDeriv (x : E2) : E2 →L[ℝ] E2 :=
  (northRadius x)⁻¹ • ContinuousLinearMap.id ℝ E2 -
    ((northRadius x)^3)⁻¹ • (innerSL ℝ x).smulRight x

private theorem p6rad_hasFDerivAt_northContraction (x : E2) :
    HasFDerivAt p6rad_northContraction (p6rad_northContractionDeriv x) x := by
  have h := (p6rad_hasFDerivAt_northRadius_inv x).smul (hasFDerivAt_id x)
  apply h.congr_fderiv
  ext v i
  simp [p6rad_northContractionDeriv, sub_eq_add_neg, smul_eq_mul, mul_assoc]

private theorem p6rad_fderiv_northContraction (x : E2) :
    fderiv ℝ p6rad_northContraction x = p6rad_northContractionDeriv x :=
  (p6rad_hasFDerivAt_northContraction x).fderiv

private theorem p6rad_det_fderiv_northContraction (x : E2) :
    (fderiv ℝ p6rad_northContraction x).det = 1 / (1 + ‖x‖^2)^2 := by
  have hr := (p6rad_northRadius_pos x).ne'
  have hdet : (p6rad_northContractionDeriv x).det =
      ((northRadius x)^2 - (x 0 ^ 2 + x 1 ^ 2)) / (northRadius x)^4 := by
    rw [ContinuousLinearMap.det,
      ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
      Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, p6rad_northContractionDeriv,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right]
    field_simp [hr]
    ring
  have hnum : (northRadius x)^2 - (x 0 ^ 2 + x 1 ^ 2) = 1 := by
    rw [p6rad_northRadius_sq, p6rad_normSq2]
    ring
  rw [p6rad_fderiv_northContraction, hdet, hnum,
    show (northRadius x)^4 = (1+‖x‖^2)^2 by
      rw [show (northRadius x)^4 = ((northRadius x)^2)^2 by ring, p6rad_northRadius_sq]]

private lemma p6rad_inv_radius_cube_eq_rpow (x : E2) :
    ((northRadius x)^3)⁻¹ = (1 + ‖x‖^2) ^ ((-3 : ℝ)/2) := by
  symm
  rw [show (-3 : ℝ)/2 = -((1/2 : ℝ)*(3 : ℝ)) by norm_num,
    Real.rpow_neg (show 0 ≤ 1+‖x‖^2 by positivity),
    Real.rpow_mul (show 0 ≤ 1+‖x‖^2 by positivity),
    ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_ofNat, northRadius]

private def p6rad_coords : Plane ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

@[simp] private lemma p6rad_coords_apply (x : Plane) : p6rad_coords x = (x 0, x 1) := rfl

private lemma p6rad_coords_preserving : MeasurePreserving p6rad_coords volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

private def p6rad_planeDisk : Set Plane := {z | ‖z‖ ^ 2 < 1}
private def p6rad_heightDensity (z : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (1 - ‖z‖ ^ 2))⁻¹)

private lemma p6rad_normSq_contraction (x : Plane) :
    ‖p6rad_northContraction x‖ ^ 2 = ‖x‖ ^ 2 / (1 + ‖x‖ ^ 2) := by
  rw [p6rad_northContraction, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
    p6rad_northRadius_sq, div_eq_mul_inv, mul_comm]

private lemma p6rad_contraction_mem_disk (x : Plane) : p6rad_northContraction x ∈ p6rad_planeDisk := by
  change ‖p6rad_northContraction x‖ ^ 2 < 1
  rw [p6rad_normSq_contraction]
  apply (div_lt_one (show 0 < 1+‖x‖^2 by positivity)).2
  linarith

private lemma p6rad_contraction_height (x : Plane) :
    Real.sqrt (1 - ‖p6rad_northContraction x‖ ^ 2) = (northRadius x)⁻¹ := by
  have he : 1 - ‖p6rad_northContraction x‖ ^ 2 = ((northRadius x)⁻¹)^2 := by
    rw [p6rad_normSq_contraction, inv_pow, p6rad_northRadius_sq]
    field_simp [show 1+‖x‖^2 ≠ 0 by positivity]
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr (p6rad_northRadius_pos x))]

private lemma p6rad_contraction_left_inverse (x : Plane) :
    (Real.sqrt (1 - ‖p6rad_northContraction x‖ ^ 2))⁻¹ • p6rad_northContraction x = x := by
  rw [p6rad_contraction_height, inv_inv, p6rad_northContraction, smul_smul,
    mul_inv_cancel₀ (p6rad_northRadius_pos x).ne', one_smul]

private lemma p6rad_contraction_injective : Function.Injective p6rad_northContraction := by
  intro x y hxy
  have hh := congrArg (fun z : Plane => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • z) hxy
  simpa only [p6rad_contraction_left_inverse] using hh

private lemma p6rad_contraction_image : p6rad_northContraction '' (Set.univ : Set Plane) = p6rad_planeDisk := by
  ext z
  constructor
  · rintro ⟨x, -, rfl⟩
    exact p6rad_contraction_mem_disk x
  · intro hz
    have hz0 : 0 < 1 - ‖z‖^2 := sub_pos.mpr hz
    let h := Real.sqrt (1-‖z‖^2)
    have hh : 0 < h := Real.sqrt_pos.mpr hz0
    have hs : h^2 = 1-‖z‖^2 := Real.sq_sqrt hz0.le
    let x : Plane := h⁻¹ • z
    have hx : ‖x‖^2 = h⁻¹^2 * ‖z‖^2 := by
      dsimp [x]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh), mul_pow]
    have hr2 : northRadius x ^ 2 = (h⁻¹)^2 := by
      rw [p6rad_northRadius_sq, hx, inv_pow]
      field_simp [hh.ne']
      nlinarith [hs]
    have hr : northRadius x = h⁻¹ := by
      nlinarith [p6rad_northRadius_pos x, inv_pos.mpr hh]
    refine ⟨x, Set.mem_univ x, ?_⟩
    rw [p6rad_northContraction, hr, inv_inv]
    dsimp [x]
    rw [smul_smul, mul_inv_cancel₀ hh.ne', one_smul]

private lemma p6rad_heightDensity_coords : p6rad_heightDensity = fun x => graphDensity (p6rad_coords x) := by
  funext x
  simp only [p6rad_heightDensity, graphDensity, p6rad_coords_apply, p6rad_normSq2]
  congr 3
  ring

private lemma p6rad_measurable_heightDensity : Measurable p6rad_heightDensity := by
  unfold p6rad_heightDensity
  fun_prop

private lemma p6rad_measurable_contraction : Measurable p6rad_northContraction :=
  (continuous_iff_continuousAt.mpr
    (fun x => (p6rad_hasFDerivAt_northContraction x).continuousAt)).measurable

private lemma p6rad_jacobian_measurable :
    Measurable (fun x : Plane => ENNReal.ofReal |(p6rad_northContractionDeriv x).det|) := by
  have he (x : Plane) : (p6rad_northContractionDeriv x).det = 1/(1+‖x‖^2)^2 := by
    rw [← p6rad_fderiv_northContraction, p6rad_det_fderiv_northContraction]
  simp_rw [he]
  fun_prop

private lemma p6rad_density_factor (x : Plane) :
    ENNReal.ofReal |(p6rad_northContractionDeriv x).det| * p6rad_heightDensity (p6rad_northContraction x) =
      ENNReal.ofReal (density x) := by
  have hd : (p6rad_northContractionDeriv x).det = 1/(1+‖x‖^2)^2 := by
    rw [← p6rad_fderiv_northContraction, p6rad_det_fderiv_northContraction]
  rw [p6rad_heightDensity, p6rad_contraction_height, inv_inv, hd,
    abs_of_pos (show 0 < 1/(1+‖x‖^2)^2 by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ 1/(1+‖x‖^2)^2 by positivity)]
  congr 1
  have hden : density x = ((northRadius x)^3)⁻¹ := by
    simpa only [density, HPow.hPow, Pow.pow,
      show ((-3 : ℝ)/2) = -(3/2 : ℝ) by norm_num]
      using (p6rad_inv_radius_cube_eq_rpow x).symm
  rw [hden, ← p6rad_northRadius_sq]
  field_simp [(p6rad_northRadius_pos x).ne']

private lemma p6rad_map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (P : α → β) (g : β → ℝ≥0∞)
    (hP : Measurable P) (hg : Measurable g) :
    Measure.map P (μ.withDensity (fun x => g (P x))) =
      (Measure.map P μ).withDensity g := by
  ext1 s hs
  rw [Measure.map_apply hP hs, withDensity_apply _ (hs.preimage hP),
    withDensity_apply _ hs, setLIntegral_map hs hg hP]

private lemma p6rad_pure_planar_change :
    (volume.withDensity (fun x : Plane => ENNReal.ofReal (density x))).map p6rad_northContraction =
      ((volume : Measure Plane).restrict p6rad_planeDisk).withDensity p6rad_heightDensity := by
  have hJac := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure Plane)
    (s := Set.univ) (f := p6rad_northContraction) (f' := p6rad_northContractionDeriv)
    MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (p6rad_hasFDerivAt_northContraction x).hasFDerivWithinAt)
    (fun x _ y _ h => p6rad_contraction_injective h)
  simp only [Measure.restrict_univ, p6rad_contraction_image] at hJac
  have hfactor :
      (volume : Measure Plane).withDensity (fun x => ENNReal.ofReal (density x)) =
        ((volume : Measure Plane).withDensity
          (fun x => ENNReal.ofReal |(p6rad_northContractionDeriv x).det|)).withDensity
            (fun x => p6rad_heightDensity (p6rad_northContraction x)) := by
    rw [← withDensity_mul volume
      (f := fun x => ENNReal.ofReal |(p6rad_northContractionDeriv x).det|)
      (g := fun x => p6rad_heightDensity (p6rad_northContraction x)) p6rad_jacobian_measurable
      (p6rad_measurable_heightDensity.comp p6rad_measurable_contraction)]
    apply congrArg (Measure.withDensity volume)
    funext x
    exact (p6rad_density_factor x).symm
  rw [hfactor, p6rad_map_withDensity_comp _ _ _ p6rad_measurable_contraction p6rad_measurable_heightDensity, hJac]

private lemma p6rad_coordinate_restricted_volume :
    ((volume : Measure Plane).restrict p6rad_planeDisk).map p6rad_coords =
      (volume : Measure (ℝ × ℝ)).restrict unitDisk := by
  have he : p6rad_coords ⁻¹' unitDisk = p6rad_planeDisk := by
    ext x
    simp only [Set.mem_preimage, unitDisk, p6rad_coords_apply, Set.mem_setOf_eq, p6rad_planeDisk, p6rad_normSq2]
  have hu : MeasurableSet unitDisk := by
    unfold unitDisk
    exact measurableSet_lt (by fun_prop) measurable_const
  rw [← he, ← Measure.restrict_map p6rad_coords.measurable hu, p6rad_coords_preserving.map_eq]

private lemma p6rad_radialPair_eq (x : Plane) : radialPair x = p6rad_coords (p6rad_northContraction x) := by
  apply Prod.ext <;> simp [radialPair, p6rad_northContraction, northRadius, div_eq_mul_inv, mul_comm]

theorem proof_Gnomonic_planarRadialMeasure :
  planarMeasure.map radialPair = ((volume : Measure (ℝ × ℝ)).restrict unitDisk).withDensity graphDensity := by
  have hg : Measurable graphDensity := by unfold graphDensity; fun_prop
  calc
    planarMeasure.map radialPair = (planarMeasure.map p6rad_northContraction).map p6rad_coords := by
      rw [Measure.map_map p6rad_coords.measurable p6rad_measurable_contraction]
      apply congrArg (fun f => Measure.map f planarMeasure)
      funext x
      exact p6rad_radialPair_eq x
    _ = (((volume : Measure Plane).restrict p6rad_planeDisk).withDensity p6rad_heightDensity).map p6rad_coords := by
      rw [planarMeasure, p6rad_pure_planar_change]
    _ = (((volume : Measure Plane).restrict p6rad_planeDisk).map p6rad_coords).withDensity graphDensity := by
      rw [p6rad_heightDensity_coords]
      exact p6rad_map_withDensity_comp _ p6rad_coords graphDensity p6rad_coords.measurable hg
    _ = _ := by rw [p6rad_coordinate_restricted_volume]

#print axioms proof_Gnomonic_planarRadialMeasure
