import HardSphereB5Lean.Theorems.Thm_SolidGeom_sphere_upper_projection
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical
noncomputable section

theorem proof_SolidGeom_sphere_upper_patch_transport (c : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (A : Set E3) (hA : MeasurableSet A) (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    let P : E3 → ℝ × ℝ := fun x => (inner ℝ (e 0) x, inner ℝ (e 1) x)
    let D : Set (ℝ × ℝ) := {p | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1}
    let U : ℝ × ℝ → E3 := fun p => p.1 • e 0 + p.2 • e 1 +
      (inner ℝ (e 2) c + Real.sqrt (1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
        (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2
    let H : Set E3 := {x | 0 < inner ℝ (e 2) (x - c)}
    (∫ x in A ∩ H, F (P x) * inner ℝ (e 2) (x - c) ∂sphereMeasure c) =
      ∫ p in D, if U p ∈ A then F p else 0 := by
  classical
  dsimp only
  let P : E3 → ℝ × ℝ := fun x => (inner ℝ (e 0) x, inner ℝ (e 1) x)
  let D : Set (ℝ × ℝ) := {p | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1}
  let U : ℝ × ℝ → E3 := fun p => p.1 • e 0 + p.2 • e 1 +
    (inner ℝ (e 2) c + Real.sqrt (1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
      (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2
  let H : Set E3 := {x | 0 < inner ℝ (e 2) (x - c)}
  let ν : Measure E3 := ((sphereMeasure c).restrict H).withDensity
    (fun x => ENNReal.ofReal (inner ℝ (e 2) (x - c)))
  let g : ℝ × ℝ → ℝ := (U ⁻¹' A).indicator F
  let G : E3 → ℝ := A.indicator (fun x => F (P x))
  change (∫ x in A ∩ H, F (P x) * inner ℝ (e 2) (x - c) ∂sphereMeasure c) =
    ∫ p in D, g p
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
  have hUc : Continuous U := by fun_prop
  have hPm : Measurable P := by fun_prop
  have hgm : StronglyMeasurable g := hF.stronglyMeasurable.indicator (hA.preimage hUc.measurable)
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
  have hcmp : (fun x => g (P x)) =ᵐ[ν] G := by
    filter_upwards [hsν, hHν] with x hs hH
    simp [g, G, Set.indicator, hgraph x hs hH]
  have hdens : Measurable (fun x : E3 => ENNReal.ofReal (inner ℝ (e 2) (x - c))) := by
    fun_prop
  have hconvert : (∫ x, G x ∂ν) =
      ∫ x in H, A.indicator (fun x => F (P x) * inner ℝ (e 2) (x - c)) x ∂sphereMeasure c := by
    dsimp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul hdens
      (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top) G]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hHm] with x hx
    rw [ENNReal.toReal_ofReal (le_of_lt hx)]
    by_cases hxa : x ∈ A <;> simp [G, hxa, smul_eq_mul, mul_comm]
  have hproj := SolidGeom.sphere_upper_projection c e he
  change Measure.map P ν = (volume : Measure (ℝ × ℝ)).restrict D at hproj
  calc
    (∫ x in A ∩ H, F (P x) * inner ℝ (e 2) (x - c) ∂sphereMeasure c) =
        ∫ x in H, A.indicator (fun x => F (P x) * inner ℝ (e 2) (x - c)) x ∂sphereMeasure c := by
      rw [setIntegral_indicator hA, Set.inter_comm]
    _ = ∫ x, G x ∂ν := hconvert.symm
    _ = ∫ x, g (P x) ∂ν := integral_congr_ae hcmp.symm
    _ = ∫ p, g p ∂Measure.map P ν := (integral_map_of_stronglyMeasurable hPm hgm).symm
    _ = ∫ p in D, g p := by rw [hproj]

#print axioms proof_SolidGeom_sphere_upper_patch_transport
