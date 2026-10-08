import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SphericalCoordinates_angularPushforward
set_option autoImplicit false

open MeasureTheory SphereGeom
open scoped NNReal ENNReal

noncomputable section

theorem proof_SphereGeom_Aux_SphericalCoordinates_standardIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E3 → F) (hf : Integrable f dOmega) :
    ∫ u, f u ∂dOmega =
      ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Real.sin θ • f ((Real.sin θ * Real.cos φ) • (EuclideanSpace.basisFun (Fin 3) ℝ) 0 +
          (Real.sin θ * Real.sin φ) • (EuclideanSpace.basisFun (Fin 3) ℝ) 1 +
          Real.cos θ • (EuclideanSpace.basisFun (Fin 3) ℝ) 2) := by
  let coord : ℝ × ℝ → E3 := fun p =>
    (Real.sin p.1 * Real.cos p.2) • (EuclideanSpace.basisFun (Fin 3) ℝ) 0 +
    (Real.sin p.1 * Real.sin p.2) • (EuclideanSpace.basisFun (Fin 3) ℝ) 1 +
    Real.cos p.1 • (EuclideanSpace.basisFun (Fin 3) ℝ) 2
  let μθ : Measure ℝ := volume.restrict (Set.Ioc 0 Real.pi)
  let μφ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let μ : Measure (ℝ × ℝ) := μθ.prod μφ
  let w : ℝ × ℝ → ℝ≥0 := fun p => Real.toNNReal (Real.sin p.1)
  have hcoord : Measurable coord := by
    apply Continuous.measurable
    unfold coord
    fun_prop
  have hw : Measurable w := by
    apply Continuous.measurable
    unfold w
    fun_prop
  have hmap : (μ.withDensity (fun p => (w p : ℝ≥0∞))).map coord = dOmega :=
    SphereGeom.Aux.SphericalCoordinates.angularPushforward
  have hfm : Integrable f ((μ.withDensity (fun p => (w p : ℝ≥0∞))).map coord) := by
    rw [hmap]
    exact hf
  have hfcomp : Integrable (f ∘ coord) (μ.withDensity (fun p => (w p : ℝ≥0∞))) :=
    hfm.comp_measurable hcoord
  have hfw : Integrable (fun p => w p • f (coord p)) μ :=
    (integrable_withDensity_iff_integrable_smul hw).mp hfcomp
  calc
    ∫ u, f u ∂dOmega = ∫ p, f (coord p) ∂μ.withDensity (fun p => (w p : ℝ≥0∞)) := by
      rw [← hmap]
      exact integral_map hcoord.aemeasurable hfm.aestronglyMeasurable
    _ = ∫ p, w p • f (coord p) ∂μ := integral_withDensity_eq_integral_smul hw _
    _ = ∫ θ, ∫ φ, w (θ, φ) • f (coord (θ, φ)) ∂μφ ∂μθ := integral_prod _ hfw
    _ = _ := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro θ hθ
      dsimp only
      rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro φ _
      change (Real.toNNReal (Real.sin θ) : ℝ) • f (coord (θ, φ)) = _
      rw [Real.coe_toNNReal _ (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)]
