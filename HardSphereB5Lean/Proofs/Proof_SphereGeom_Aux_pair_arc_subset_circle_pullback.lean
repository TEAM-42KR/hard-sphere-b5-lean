import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000

theorem proof_SphereGeom_Aux_pair_arc_subset_circle_pullback (c : E3) (E : Fin 2 → E3) (hE : Orthonormal ℝ E) (r : ℝ) (hr : 0 < r)
    (A : Set E3) (hA : MeasurableSet A)
    (hsub : A ⊆ circlePt c (E 0) (E 1) r '' Set.Icc (0 : ℝ) (2 * π))
    (g : E3 × E3 → ℝ) (hg : Measurable g) :
    (∫ u in A, ∫ v in A, g (u, v) ∂arcMeasure ∂arcMeasure) = r ^ 2 *
      ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
        if circlePt c (E 0) (E 1) r t ∈ A ∧ circlePt c (E 0) (E 1) r s ∈ A
        then g (circlePt c (E 0) (E 1) r t, circlePt c (E 0) (E 1) r s) else 0 := by
  let I : Set ℝ := Set.Icc 0 (2 * π)
  let γ : ℝ → E3 := circlePt c (E 0) (E 1) r
  have hγ : Measurable γ := by dsimp [γ]; unfold circlePt; fun_prop
  have hm : arcMeasure.restrict (γ '' I) =
      ENNReal.ofReal r • (volume.restrict I).map γ :=
    SphereGeom.arcMeasure_restrict_circle c E hE r hr 0 (2 * π)
      (by positivity) (by simp)
  have one (k : E3 → ℝ) (hk : Measurable k) :
      (∫ u in A, k u ∂arcMeasure) = r * ∫ t in I, A.indicator k (γ t) := by
    calc
      (∫ u in A, k u ∂arcMeasure) = ∫ u in A, k u ∂(arcMeasure.restrict (γ '' I)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
      _ = ∫ u, A.indicator k u ∂(arcMeasure.restrict (γ '' I)) := (integral_indicator hA).symm
      _ = r * ∫ t in I, A.indicator k (γ t) := by
        rw [hm, integral_smul_measure, ENNReal.toReal_ofReal hr.le, smul_eq_mul,
          integral_map_of_stronglyMeasurable hγ (hk.stronglyMeasurable.indicator hA)]
  let Q : E3 → ℝ := fun u => ∫ s in I, A.indicator (fun v => g (u, v)) (γ s)
  have hQI : Measurable (fun z : E3 × ℝ => A.indicator (fun v => g (z.1, v)) (γ z.2)) := by
    apply (hg.comp (measurable_fst.prodMk (hγ.comp measurable_snd))).ite
      (hA.preimage (hγ.comp measurable_snd)) measurable_const
  have hQ : Measurable Q := hQI.stronglyMeasurable.integral_prod_right'.measurable
  have hinner (u : E3) : (∫ v in A, g (u, v) ∂arcMeasure) = r * Q u :=
    one _ (hg.comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  rw [integral_const_mul, one Q hQ]
  have hind (t : ℝ) : A.indicator Q (γ t) =
      ∫ s in I, if γ t ∈ A ∧ γ s ∈ A then g (γ t, γ s) else 0 := by
    by_cases ht : γ t ∈ A <;> simp [Q, Set.indicator, ht]
  simp_rw [hind]
  dsimp [I, γ]
  ring
