import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
set_option autoImplicit false
open SphereGeom (E3 dOmega)
open Gnomonic
open MeasureTheory

private lemma density_measurable : Measurable density := by
  unfold density
  exact ((continuous_const.add (continuous_norm.pow 2)).rpow_const
    (fun x => Or.inl (show (1 : ℝ) + ‖x‖ ^ 2 ≠ 0 by positivity))).measurable

private lemma density_nonneg (x : Plane) : 0 ≤ density x := by
  unfold density
  exact Real.rpow_nonneg (by positivity) _

theorem proof_Gnomonic_integralFromChartMeasure (R : E3 ≃ₗᵢ[ℝ] E3)
    (hm : Measurable (inverseFrame R))
    (hleft : ∀ u ∈ hemisphereFrame R, inverseFrame R (chartFrame R u) = u)
    (hright : ∀ x, chartFrame R (inverseFrame R x) = x)
    (hchart : planarMeasure.map (inverseFrame R) = dOmega.restrict (hemisphereFrame R))
    (U : Set E3) (hU : MeasurableSet U) (hsub : U ⊆ hemisphereFrame R)
    (f : E3 → ℝ) (hf : IntegrableOn f U dOmega) :
    ∫ u in U, f u ∂dOmega =
      ∫ x in chartFrame R '' U, density x * f (inverseFrame R x) := by
  classical
  have himage : chartFrame R '' U = inverseFrame R ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      change inverseFrame R (chartFrame R u) ∈ U
      rw [hleft u (hsub hu)]
      exact hu
    · intro hx
      exact ⟨inverseFrame R x,hx,hright x⟩
  have hImg : MeasurableSet (chartFrame R '' U) := by rw [himage]; exact hU.preimage hm
  have hi : Integrable (U.indicator f) dOmega := (integrable_indicator_iff hU).mpr hf
  have him : Integrable (U.indicator f) (planarMeasure.map (inverseFrame R)) := by
    rw [hchart]
    exact hi.mono_measure Measure.restrict_le_self
  have hcomp : (fun x => U.indicator f (inverseFrame R x)) =
      (chartFrame R '' U).indicator (fun x => f (inverseFrame R x)) := by
    ext x
    by_cases hx : inverseFrame R x ∈ U <;> simp [Set.indicator,himage,hx]
  calc
    ∫ u in U, f u ∂dOmega = ∫ u, U.indicator f u ∂dOmega := (integral_indicator hU).symm
    _ = ∫ u, U.indicator f u ∂dOmega.restrict (hemisphereFrame R) := by
      rw [setIntegral_indicator hU, Set.inter_eq_right.mpr hsub, integral_indicator hU]
    _ = ∫ u, U.indicator f u ∂planarMeasure.map (inverseFrame R) := by rw [hchart]
    _ = ∫ x, U.indicator f (inverseFrame R x) ∂planarMeasure :=
      integral_map hm.aemeasurable him.aestronglyMeasurable
    _ = ∫ x, density x * U.indicator f (inverseFrame R x) := by
      unfold planarMeasure
      have hdm : Measurable (fun x : Plane => ENNReal.ofReal (density x)) :=
        ENNReal.measurable_ofReal.comp density_measurable
      rw [integral_withDensity_eq_integral_toReal_smul hdm
        (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top)
        (fun x => U.indicator f (inverseFrame R x))]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [ENNReal.toReal_ofReal (density_nonneg x),smul_eq_mul]
    _ = ∫ x in chartFrame R '' U, density x * f (inverseFrame R x) := by
      rw [← integral_indicator hImg]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : inverseFrame R x ∈ U <;> simp [Set.indicator,himage,hx]

