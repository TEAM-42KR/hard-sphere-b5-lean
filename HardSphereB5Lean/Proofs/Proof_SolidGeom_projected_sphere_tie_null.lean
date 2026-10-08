import HardSphereB5Lean.Theorems.Thm_SolidGeom_sphere_upper_projection
import HardSphereB5Lean.Theorems.Thm_SolidGeom_sphereMeasure_sphere_inter_null
set_option autoImplicit false
open MeasureTheory Real SphereGeom

noncomputable section

theorem proof_SolidGeom_projected_sphere_tie_null (c d : E3) (hcd : c ≠ d) (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    let D : Set (ℝ × ℝ) := {p | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1}
    let U : ℝ × ℝ → E3 := fun p => p.1 • e 0 + p.2 • e 1 +
      (inner ℝ (e 2) c + Real.sqrt (1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
        (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2
    (volume : Measure (ℝ × ℝ)) {p | p ∈ D ∧ U p ∈ Metric.sphere d 1} = 0 := by
  classical
  dsimp only
  let D : Set (ℝ × ℝ) := {p | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1}
  let U : ℝ × ℝ → E3 := fun p => p.1 • e 0 + p.2 • e 1 +
    (inner ℝ (e 2) c + Real.sqrt (1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
      (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2
  let P : E3 → ℝ × ℝ := fun x => (inner ℝ (e 0) x, inner ℝ (e 1) x)
  let H : Set E3 := {x | 0 < inner ℝ (e 2) (x - c)}
  let ν : Measure E3 := ((sphereMeasure c).restrict H).withDensity
    (fun x => ENNReal.ofReal (inner ℝ (e 2) (x - c)))
  let A : Set (ℝ × ℝ) := {p | p ∈ D ∧ U p ∈ Metric.sphere d 1}
  change (volume : Measure (ℝ × ℝ)) A = 0
  let b : OrthonormalBasis (Fin 3) ℝ E3 :=
    (basisOfOrthonormalOfCardEqFinrank he (by simp [E3])).toOrthonormalBasis (by simpa using he)
  have hb (i : Fin 3) : b i = e i := by simp [b]
  have hgraph (x : E3) (hs : x ∈ Metric.sphere c 1)
      (hh : 0 < inner ℝ (e 2) (x - c)) : U (P x) = x := by
    have hnorm : ‖x - c‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hs
    have hsum : (inner ℝ (e 0) x - inner ℝ (e 0) c) ^ 2 +
        (inner ℝ (e 1) x - inner ℝ (e 1) c) ^ 2 +
        (inner ℝ (e 2) (x - c)) ^ 2 = 1 := by
      simpa [Fin.sum_univ_three, hb, inner_sub_right, hnorm] using b.sum_sq_inner_right (x - c)
    have hr : 1 - (inner ℝ (e 0) x - inner ℝ (e 0) c) ^ 2 -
        (inner ℝ (e 1) x - inner ℝ (e 1) c) ^ 2 =
        (inner ℝ (e 2) (x - c)) ^ 2 := by linarith
    have hsqrt : Real.sqrt (1 - (inner ℝ (e 0) x - inner ℝ (e 0) c) ^ 2 -
        (inner ℝ (e 1) x - inner ℝ (e 1) c) ^ 2) = inner ℝ (e 2) (x - c) := by
      rw [hr, Real.sqrt_sq (le_of_lt hh)]
    have hcoeff : inner ℝ (e 2) c + inner ℝ (e 2) (x - c) = inner ℝ (e 2) x := by
      simp [inner_sub_right]
    dsimp only [U, P]
    rw [hsqrt, hcoeff]
    simpa [Fin.sum_univ_three, hb, add_assoc] using b.sum_repr' x
  have hHm : MeasurableSet H := by
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hDm : MeasurableSet D := by
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hUc : Continuous U := by fun_prop
  have hAm : MeasurableSet A := hDm.inter (Metric.isClosed_sphere.measurableSet.preimage hUc.measurable)
  have hPm : Measurable P := by fun_prop
  have hsc : ∀ᵐ x ∂sphereMeasure c, x ∈ Metric.sphere c 1 := by
    rw [sphereMeasure]
    have ht : Measurable (fun u : Metric.sphere (0 : E3) 1 => c + (u : E3)) := by fun_prop
    apply (ae_map_iff ht.aemeasurable Metric.isClosed_sphere.measurableSet).2
    filter_upwards [] with u
    simpa [Metric.mem_sphere, dist_eq_norm] using u.property
  have hw : ν ≪ (sphereMeasure c).restrict H := withDensity_absolutelyContinuous _ _
  have hac : ν ≪ sphereMeasure c := hw.trans Measure.absolutelyContinuous_restrict
  have hsν : ∀ᵐ x ∂ν, x ∈ Metric.sphere c 1 := hac.ae_le hsc
  have hHν : ∀ᵐ x ∂ν, x ∈ H := hw.ae_le (ae_restrict_mem hHm)
  have hdν : ∀ᵐ x ∂ν, x ∉ Metric.sphere d 1 :=
    measure_eq_zero_iff_ae_notMem.mp (hac (SolidGeom.sphereMeasure_sphere_inter_null c d hcd))
  have hnull : ν (P ⁻¹' A) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hsν, hHν, hdν] with x hs hH hd
    intro hx
    have ht : U (P x) ∈ Metric.sphere d 1 := hx.2
    rw [hgraph x hs hH] at ht
    exact hd ht
  have hproj := SolidGeom.sphere_upper_projection c e he
  change Measure.map P ν = (volume : Measure (ℝ × ℝ)).restrict D at hproj
  have hn : (volume : Measure (ℝ × ℝ)).restrict D A = 0 := by
    rw [← hproj, Measure.map_apply hPm hAm]
    exact hnull
  rw [Measure.restrict_apply hAm, Set.inter_eq_left.mpr (show A ⊆ D from fun _ h => h.1)] at hn
  exact hn

#print axioms proof_SolidGeom_projected_sphere_tie_null
