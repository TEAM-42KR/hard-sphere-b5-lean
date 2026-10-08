import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_lintegral_encard_greatCircle_sigmaCompact
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_monotone_eq_measure_on_measurable_of_sigmaCompact
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option backward.isDefEq.respectTransparency false in
theorem proof_SphereGeom_Aux_Crofton_lintegral_encard_greatCircle_image (γ : ℝ → E3) (a b : ℝ)
    (hγ : ContDiff ℝ 1 γ) (hs : ∀ t ∈ Set.Icc a b, ‖γ t‖ = 1)
    (hreg : ∀ t ∈ Set.Icc a b, deriv γ t ≠ 0) (hinj : Set.InjOn γ (Set.Icc a b))
    (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b) :
    ∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega =
      4 * ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := by
  let w : ℝ → ENNReal := fun t => ENNReal.ofReal ‖deriv γ t‖
  let ν : Measure ℝ := (4 : ENNReal) • ((volume.withDensity w).restrict (Set.Icc a b))
  let F : Set ℝ → ENNReal := fun T => ∫⁻ p, ((greatCircle p ∩ γ '' T).encard : ENNReal) ∂dOmega
  have hw : Measurable w := (measurable_deriv γ).norm.ennreal_ofReal
  have hnint : IntegrableOn (deriv γ) (Set.Icc a b) := hγ.continuous_deriv_one.integrableOn_Icc
  have hfinite : (∫⁻ t in Set.Icc a b, w t) < ⊤ :=
    (hasFiniteIntegral_iff_norm (deriv γ)).mp hnint.hasFiniteIntegral
  haveI : IsFiniteMeasure ν := by
    constructor
    change ((4 : ENNReal) • ((volume.withDensity w).restrict (Set.Icc a b))) Set.univ < ⊤
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      withDensity_apply _ measurableSet_Icc]
    exact ENNReal.mul_lt_top (by norm_num) hfinite
  have hν (T : Set ℝ) (hTm : MeasurableSet T) (hTsub : T ⊆ Set.Icc a b) :
      ν T = 4 * ∫⁻ t in T, w t := by
    change ((4 : ENNReal) • ((volume.withDensity w).restrict (Set.Icc a b))) T = _
    rw [Measure.smul_apply, Measure.restrict_apply hTm, Set.inter_eq_left.mpr hTsub,
      withDensity_apply _ hTm]
    rfl
  have hF : Monotone F := by
    intro T U hTU
    apply lintegral_mono
    intro p
    exact ENat.toENNReal_mono (Set.encard_mono
      (Set.inter_subset_inter_right _ (Set.image_mono hTU)))
  have hEq : ∀ T : Set ℝ, T ⊆ Set.Icc a b → IsSigmaCompact T → F T = ν T := by
    intro T hTsub hTc
    have hTm : MeasurableSet T := by
      obtain ⟨K, hK, hKu⟩ := hTc
      rw [← hKu]
      exact MeasurableSet.iUnion (fun n => (hK n).measurableSet)
    rw [hν T hTm hTsub]
    exact SphereGeom.Aux.Crofton.lintegral_encard_greatCircle_sigmaCompact γ a b
      hγ hs hreg hinj T hTm hTsub hTc
  calc
    F S = ν S := SphereGeom.Aux.Crofton.monotone_eq_measure_on_measurable_of_sigmaCompact
      F hF ν a b hEq S hS hSab
    _ = 4 * ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := hν S hS hSab
