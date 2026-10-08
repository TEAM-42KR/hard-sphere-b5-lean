import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000
theorem proof_SphereGeom_Aux_pair_arcs_subsets_circles_pullback
(cA cB : E3) (EA EB : Fin 2 → E3) (hEA : Orthonormal ℝ EA) (hEB : Orthonormal ℝ EB)
(rA rB : ℝ) (hrA : 0 < rA) (hrB : 0 < rB)
(A B : Set E3) (hA : MeasurableSet A) (hB : MeasurableSet B)
(hsubA : A ⊆ circlePt cA (EA 0) (EA 1) rA '' Set.Icc (0 : ℝ) (2 * π))
(hsubB : B ⊆ circlePt cB (EB 0) (EB 1) rB '' Set.Icc (0 : ℝ) (2 * π))
(g : E3 × E3 → ℝ) (hg : Measurable g) :
(∫ u in A, ∫ v in B, g (u,v) ∂arcMeasure ∂arcMeasure) =
rA * rB * ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
if circlePt cA (EA 0) (EA 1) rA t ∈ A ∧ circlePt cB (EB 0) (EB 1) rB s ∈ B
then g (circlePt cA (EA 0) (EA 1) rA t, circlePt cB (EB 0) (EB 1) rB s) else 0  := by
  let I : Set ℝ := Set.Icc 0 (2 * π)
  let γA : ℝ → E3 := circlePt cA (EA 0) (EA 1) rA
  let γB : ℝ → E3 := circlePt cB (EB 0) (EB 1) rB
  have hγB : Measurable γB := by dsimp [γB]; unfold circlePt; fun_prop
  have one (c : E3) (E : Fin 2 → E3) (hE : Orthonormal ℝ E) (r : ℝ) (hr : 0 < r)
      (A : Set E3) (hA : MeasurableSet A)
      (hsub : A ⊆ circlePt c (E 0) (E 1) r '' I) (k : E3 → ℝ) (hk : Measurable k) :
      (∫ u in A, k u ∂arcMeasure) = r * ∫ t in I, A.indicator k (circlePt c (E 0) (E 1) r t) := by
    let γ : ℝ → E3 := circlePt c (E 0) (E 1) r
    have hγ : Measurable γ := by dsimp [γ]; unfold circlePt; fun_prop
    have hm : arcMeasure.restrict (γ '' I) =
        ENNReal.ofReal r • (volume.restrict I).map γ :=
      SphereGeom.arcMeasure_restrict_circle c E hE r hr 0 (2 * π) (by positivity) (by simp)
    calc
      (∫ u in A, k u ∂arcMeasure) = ∫ u in A, k u ∂(arcMeasure.restrict (γ '' I)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
      _ = ∫ u, A.indicator k u ∂(arcMeasure.restrict (γ '' I)) := (integral_indicator hA).symm
      _ = r * ∫ t in I, A.indicator k (γ t) := by
        rw [hm, integral_smul_measure, ENNReal.toReal_ofReal hr.le, smul_eq_mul,
          integral_map_of_stronglyMeasurable hγ (hk.stronglyMeasurable.indicator hA)]
  let Q : E3 → ℝ := fun u => ∫ s in I, B.indicator (fun v => g (u,v)) (γB s)
  have hQI : Measurable (fun z : E3 × ℝ => B.indicator (fun v => g (z.1,v)) (γB z.2)) := by
    apply (hg.comp (measurable_fst.prodMk (hγB.comp measurable_snd))).ite
      (hB.preimage (hγB.comp measurable_snd)) measurable_const
  have hQ : Measurable Q := hQI.stronglyMeasurable.integral_prod_right'.measurable
  have hinner (u : E3) : (∫ v in B, g (u,v) ∂arcMeasure) = rB * Q u :=
    one cB EB hEB rB hrB B hB hsubB _ (hg.comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  rw [integral_const_mul, one cA EA hEA rA hrA A hA hsubA Q hQ]
  have hind (t : ℝ) : A.indicator Q (γA t) =
      ∫ s in I, if γA t ∈ A ∧ γB s ∈ B then g (γA t,γB s) else 0 := by
    by_cases ht : γA t ∈ A <;> simp [Q, Set.indicator, ht]
  change rB * (rA * ∫ t in I, A.indicator Q (γA t)) = _
  simp_rw [hind]
  dsimp [I, γA, γB]
  ring
